import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense
import Mathlib.Analysis.Normed.Lp.PiLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem denseRange_ccTensorToHs_piLp
    (g : SmoothRiemannianMetric I M) (s : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (p : ℝ≥0∞) :
    DenseRange (fun S : ι → SmoothCcTensor g 0 s =>
      WithLp.toLp p (fun i => ccTensorToHs (I := I) (M := M) g s σ (S i))) := by
  have h : DenseRange (fun S : ι → SmoothCcTensor g 0 s =>
      fun i => ccTensorToHs (I := I) (M := M) g s σ (S i)) :=
    DenseRange.piMap (fun _ : ι => ccToHsLin_dense (I := I) (M := M) g s hσ)
  exact ((PiLp.homeomorph p (fun _ : ι => TensorHs g 0 s σ)).symm.surjective.denseRange).comp
    h (PiLp.continuous_toLp p _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.denseRange_ccTensorToHs_piLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.denseRange_ccTensorToHs_piLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.denseRange_ccTensorToHs_piLp ``Submission.DifferentialGeometry.Analysis.Spectral.denseRange_ccTensorToHs_piLp

end DifferentialGeometry.Analysis.Spectral
