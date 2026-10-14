import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.BufferedReference
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem metric_eq_of_ricci_flat_of_complete_bounded_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b u v : ℝ} (hu : u ∈ _root_.Set.Ioo a b) (hv : v ∈ _root_.Set.Ioo a b) (huv : u ≤ v)
    (hreg : _root_.Set.Ioo a b ⊆ D.regular)
    (hcomplete : ∀ t ∈ _root_.Set.Ioo a b, RiemannianMetricComplete (S.family.metric t))
    (hbound : ∀ r s, a < r → r < s → s < b →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ _root_.Set.Icc r s, ∀ x : M,
        normSq0S (I := I) (S.family.metric t) x 4
          (metricRm04At (S.family.metric t) x) ≤ C)
    (hRicci : ∀ (x : M) (w z : TangentSpace I x),
      ricciTensor (S.family.metric u) x w z = 0) :
    S.family.metric v = S.family.metric u := by
  obtain ⟨c, hvc, hcb⟩ := exists_between hv.2
  have huc : u < c := huv.trans_lt hvc
  let U := SolutionOn.const (S.family.metric u) (RealTimeInterval.closedOpen u c huc)
  have hU : IsSolutionOn U :=
    isSolutionOn_const_of_ricciTensor_eq_zero (S.family.metric u) hRicci _
  obtain ⟨C, hC, hcurv⟩ := hbound u c hu.1 huc hcb
  have hUbound : ∀ t ∈ _root_.Set.Ico u c, ∀ x : M,
      normSq0S (U.base.metric t) x 4 (U.base.rm04 t x) ≤ C := by
    intro t _ x
    exact hcurv u ⟨le_rfl, huc.le⟩ x
  have heq := forward_unique_on_closedOpen_of_complete_bounded_curvature_of_buffered_reference
    huc U S hU hS hu hcb hreg hcomplete hbound hC hUbound rfl
  exact (heq v ⟨huv, hvc⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metric_eq_of_ricci_flat_of_complete_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metric_eq_of_ricci_flat_of_complete_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metric_eq_of_ricci_flat_of_complete_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.metric_eq_of_ricci_flat_of_complete_bounded_curvature

end DifferentialGeometry.PDE.RicciFlow
