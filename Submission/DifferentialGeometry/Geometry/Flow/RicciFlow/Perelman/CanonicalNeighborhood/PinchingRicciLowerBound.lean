import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciLowerBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Filter

theorem exists_forall_rescalePinchingFunction_le_of_tendsto {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi) {Q : ℕ → ℝ} (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (B δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in _root_.Filter.atTop, ∀ u : ℝ, u ≤ B → rescalePinchingFunction (Q n) Phi u ≤ δ := by
  obtain ⟨Q0, hQ0, hle⟩ := exists_forall_rescalePinchingFunction_le hPhi (B := _root_.Max.max B 0) hδ
  filter_upwards [hQ.eventually_ge_atTop Q0] with n hn u hu
  have hpos : 0 < Q n := hQ0.trans_le hn
  calc
    rescalePinchingFunction (Q n) Phi u ≤ rescalePinchingFunction (Q n) Phi (_root_.Max.max B 0) :=
      mul_le_mul_of_nonneg_left
        (hPhi.mono (mul_le_mul_of_nonneg_left (hu.trans (le_max_left B 0)) hpos.le))
        (inv_nonneg.mpr hpos.le)
    _ ≤ δ := hle (Q n) hn (_root_.Max.max B 0) ⟨le_max_right B 0, le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.exists_forall_rescalePinchingFunction_le_of_tendsto

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

theorem neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt {M : Type*}
    [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I3 M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ)
    (u : TangentSpace I3 x) :
    -(2 * δ) * g.inner x u u ≤ metricRicciAt g x (vec2 u u) := by
  have hric := neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt g x h u
  have hdim : Module.finrank ℝ ThreeSpace = 3 := finrank_euclideanSpace_fin
  rw [hdim] at hric
  norm_num at hric
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.neg_two_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
