import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem tensorHsInclusion_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (s : ℕ) {τ σ : ℝ} (h : τ ≤ σ) (S : SmoothCcTensor g 0 s) :
    tensorHsInclusion h (ccTensorToHs (I := I) (M := M) g s σ S) =
      ccTensorToHs (I := I) (M := M) g s τ S := by
  ext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff, ccTensorToHs_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_ccTensorToHs ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_ccTensorToHs

end DifferentialGeometry.Analysis.Spectral

end
