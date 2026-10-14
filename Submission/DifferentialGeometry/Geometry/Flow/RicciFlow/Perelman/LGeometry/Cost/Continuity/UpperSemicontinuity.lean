import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.Action
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.NoAdmissibleCurve
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff
import Mathlib.Topology.Semicontinuity.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem upperSemicontinuous_lCost_of_complete_bounded_curvature
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : ℝ) (htau : 0 < tau)
    (hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ _root_.Set.Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K) :
    UpperSemicontinuous (fun y : M ↦ lCost S T x y tau) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    exact continuous_of_discreteTopology.upperSemicontinuous
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  let _ : T2Space (TangentBundle I M) := inferInstance
  intro y
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  by_cases hreach : ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧ alpha b = y
  · obtain ⟨alpha₀, halpha₀, ha₀, hb₀⟩ := hreach
    obtain ⟨Z, hmin, hExp⟩ :=
      exists_lMinimizingVector_rm (I := I) S hS K T hg tau htau hreg hRm
        x y alpha₀ halpha₀ ha₀ hb₀
    let s0 : Real := Real.sqrt tau / 2
    have hs00 : 0 < s0 := by
      exact div_pos (Real.sqrt_pos.2 htau) (by norm_num)
    have hs0b : s0 < Real.sqrt tau := by
      exact div_two_lt_of_pos (Real.sqrt_pos.2 htau)
    obtain ⟨U, hUopen, hcenter, F, hF, hFcenter, hupper⟩ :=
      exists_contMDiffOn_lCost_upper_support (IM := I) S hS K T x hmin hreg hRm hs00 hs0b
    have hyU : y ∈ U := by
      rw [← hExp]
      exact hcenter
    have hFy : F y = lCost S T x y tau := by
      simpa only [hExp] using hFcenter
    intro A hA
    have hFA : F y < A := by simpa only [hFy] using hA
    have hFcont : ContinuousAt F y :=
      hF.continuousOn.continuousAt (hUopen.mem_nhds hyU)
    filter_upwards [hUopen.mem_nhds hyU,
      hFcont.eventually (Iio_mem_nhds hFA)] with z hzU hzF
    exact lt_of_le_of_lt (hupper z hzU) hzF
  · have hregSq : ∀ s ∈ _root_.Set.Icc (0 : ℝ) b, T - s ^ 2 ∈ D.regular := by
      intro s hs
      apply hreg
      have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
      constructor <;> nlinarith [sq_nonneg s]
    have hno : ¬ ∃ alpha : ℝ → M,
        ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧ alpha 0 = x ∧
          alpha b = (extChartAt I y).symm (extChartAt I y y) := by
      simpa only [extChartAt_to_inv] using hreach
    obtain ⟨ε, hε, hnoBall⟩ := lNoCurve_nhds S hS T x b hb hregSq y
      (mem_extChartAt_target y) hno
    have hyCost : lCost S T x y tau = 0 := by
      rw [← hb2]
      exact lCost_zero_no_curve S T x y b hb hreach
    intro A hA
    have hcont := (continuousAt_extChartAt (I := I) y).eventually
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    filter_upwards [hcont, (isOpen_extChartAt_source (I := I) y).mem_nhds
      (mem_extChartAt_source y)] with z hz hzs
    have hzCost : lCost S T x z tau = 0 := by
      rw [← (extChartAt I y).left_inv hzs, ← hb2]
      exact lCost_zero_no_curve S T x ((extChartAt I y).symm (extChartAt I y z))
        b hb (hnoBall (extChartAt I y z) hz)
    simpa only [hyCost, hzCost] using hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.upperSemicontinuous_lCost_of_complete_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.upperSemicontinuous_lCost_of_complete_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.upperSemicontinuous_lCost_of_complete_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.upperSemicontinuous_lCost_of_complete_bounded_curvature

end DifferentialGeometry.PDE.RicciFlow.Perelman
