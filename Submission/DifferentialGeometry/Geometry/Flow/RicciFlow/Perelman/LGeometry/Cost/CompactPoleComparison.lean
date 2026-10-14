import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.DynamicProgramming
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.UpperSemicontinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.CarrierIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem exists_lCost_basepoint_add_bound_of_compact
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hregular : _root_.Set.Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : M, 0 ≤ S.scalar t y) (p : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p' q : M, ∀ tau : ℝ, 1 < tau →
      lCost S T p q tau ≤ lCost S T p' q tau + C := by
  let : SigmaCompactSpace M := inferInstance
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  have hreg (tau : ℝ) : _root_.Set.Icc (T - tau) T ⊆ D.regular := fun _ ht => hregular ht.2
  obtain ⟨K0, _, hK0⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn S hS (hreg 1)
  have husc := upperSemicontinuous_lCost_of_complete_bounded_curvature S hS K0 T
    (RiemannianMetricComplete.of_compact (S.base.metric T)) p 1 zero_lt_one (hreg 1) hK0
  obtain ⟨C, hC⟩ := (husc.upperSemicontinuousOn _root_.Set.univ).bddAbove_of_isCompact (isCompact_univ : IsCompact (_root_.Set.univ : Set M))
  have hbound (y : M) : lCost S T p y 1 ≤ _root_.Max.max C 0 :=
    (hC (_root_.Set.mem_image_of_mem (fun y => lCost S T p y 1) (_root_.Set.mem_univ y))).trans (le_max_left _ _)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p' q tau htau
  have htau0 : 0 < tau := zero_lt_one.trans htau
  have hroot : 1 < Real.sqrt tau := (Real.lt_sqrt zero_le_one).mpr (by simpa using htau)
  have hroot2 : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau0.le
  obtain ⟨K, _, hK⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn S hS (hreg tau)
  by_contra hnot
  have hcost : lCost S T p' q tau < lCost S T p q tau - _root_.Max.max C 0 := by linarith
  obtain ⟨alpha, halpha, ha0, haend, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T p' q tau htau0 _ hcost
  have htime (a b : ℝ) : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.carrier :=
    fun s _ => D.regular_subset (hregular (sub_le_self T (sq_nonneg s)))
  have hint01 := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T 0 1 zero_le_one alpha halpha.contMDiffOn (htime 0 1)
  have hint1r := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one_of_carrier
    S hS.smoothMetric ⟨hS.scalarCont⟩ T 1 (Real.sqrt tau) hroot.le alpha halpha.contMDiffOn (htime 1 _)
  have hnonneg : 0 ≤ lRegularizedAction S T alpha 0 1 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro s _
    exact add_nonneg (mul_nonneg (by norm_num) (metric_inner_self_nonneg _ _ _))
      (mul_nonneg (by positivity) (hscalar _ (sub_le_self T (sq_nonneg s)) _))
  have hsum := lRegularizedAction_add S T alpha 0 1 (Real.sqrt tau) hint01 hint1r
  have hjoin := lCost_le_add_lRegularizedAction_of_curvature_bound_on_carrier
    S hS K T zero_lt_one hroot
    (by simpa only [hroot2] using (hreg tau).trans D.regular_subset)
    (by simpa only [hroot2, SolutionFamily.rm04, metricRm04_apply, SolutionOn.family_metric] using hK) p alpha halpha
  rw [hroot2, haend, one_pow] at hjoin
  have hb := hbound (alpha 1)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lCost_basepoint_add_bound_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lCost_basepoint_add_bound_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lCost_basepoint_add_bound_of_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_lCost_basepoint_add_bound_of_compact

end DifferentialGeometry.PDE.RicciFlow.Perelman
