import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem tensorHsToL2_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (S : SmoothCcTensor g 0 s) :
    tensorHsToL2 (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s) hσ
      (ccTensorToHs (I := I) (M := M) g s σ S) = SmoothCcTensor.toL2 S := by
  apply (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)).repr.injective
  ext i
  change tensorL2Coeff _ (tensorHsToL2 _ hσ (ccTensorToHs g s σ S)) i = _
  rw [tensorHsToL2_tensorL2Coeff, ccTensorToHs_coeff]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHsToL2_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHsToL2_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHsToL2_ccTensorToHs ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHsToL2_ccTensorToHs

end DifferentialGeometry.Analysis.Spectral
