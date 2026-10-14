import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bochner.LaplacianIterateLadder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem cc_toHs_eq_smooth
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ T =
      smoothCcToTensorHs (I := I) (M := M) g σ T := by
  refine TensorHs.ext ?_
  funext i
  simp only [ccTensorToHs_coeff, smoothCcToTensorHs_coeff]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.cc_toHs_eq_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.cc_toHs_eq_smooth target :: scope.openDecls } }

theorem cc_h1_jet_sq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) T‖ ^ 2 =
      ‖T‖ ^ 2 + ‖covGrad (I := I) (M := M) g 0 2 T‖ ^ 2 := by
  rw [cc_toHs_eq_smooth (I := I) (M := M) g (1 : ℝ) T]
  have h := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
    (I := I) (M := M) g 0 T
  simp only [oneMinusConnLapSmoothIter_zero, SmoothCcTensor.norm_toL2] at h
  have horder : (((2 * 0 + 1 : ℕ) : ℝ)) = (1 : ℝ) := by norm_num
  rw [horder] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.cc_h1_jet_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.cc_h1_jet_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.cc_h1_jet_sq ``Submission.DifferentialGeometry.Analysis.Spectral.cc_h1_jet_sq

end DifferentialGeometry.Analysis.Spectral

end
