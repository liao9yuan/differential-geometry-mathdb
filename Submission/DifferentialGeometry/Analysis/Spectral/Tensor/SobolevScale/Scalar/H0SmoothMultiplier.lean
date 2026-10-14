import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ContinuousMultiplier
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.Application

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem tensorHsInclusion_appHs_scalarCc_zero
    (g : SmoothRiemannianMetric I M) (a : C^∞⟮I, M; ℝ⟯)
    (u : TensorHs g 0 0 ((0 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    J (appHs g 0 0 0 (scalarCc g a) u) =
      scalarH0ContinuousMul g ⟨a, a.2.continuous⟩ (J u) := by
  intro J
  refine (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq (J.continuous.comp (appHs g 0 0 0 (scalarCc g a)).continuous)
      ((scalarH0ContinuousMul g ⟨a, a.2.continuous⟩).continuous.comp J.continuous)
  intro S
  simp only [ccToHsLin_apply, J, appHs_apply_ccTensorToHs, app_scalarCc,
    tensorHsInclusion_ccTensorToHs, scalarH0ContinuousMul_ccTensorToHs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_appHs_scalarCc_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_appHs_scalarCc_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_appHs_scalarCc_zero ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHsInclusion_appHs_scalarCc_zero

end DifferentialGeometry.Analysis.Spectral
