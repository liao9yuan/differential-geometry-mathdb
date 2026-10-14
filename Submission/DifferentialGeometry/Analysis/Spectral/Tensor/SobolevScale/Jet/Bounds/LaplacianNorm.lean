import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

theorem ccTensorToHs_add_two_norm_eq_oneMinusConnLap (g : SmoothRiemannianMetric I M)
    (s : ℕ) (σ : ℝ) (S : SmoothCcTensor g 0 s) :
    ‖ccTensorToHs g s (σ + 2) S‖ =
      ‖ccTensorToHs g s σ (oneMinusConnLapSmooth g 0 s S)‖ := by
  have hsq : ‖ccTensorToHs g s (σ + 2) S‖ ^ 2 =
      ‖ccTensorToHs g s σ (oneMinusConnLapSmooth g 0 s S)‖ ^ 2 := by
    rw [ccToHs_norm_sq, ccToHs_norm_sq]
    apply tsum_congr
    intro i
    rw [oneMinus_coeff]
    unfold tensorSobolevWeight
    rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one (one_le_one_add_lambda i)), Real.rpow_two]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ccTensorToHs_add_two_norm_eq_oneMinusConnLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ccTensorToHs_add_two_norm_eq_oneMinusConnLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ccTensorToHs_add_two_norm_eq_oneMinusConnLap ``Submission.DifferentialGeometry.Analysis.Spectral.ccTensorToHs_add_two_norm_eq_oneMinusConnLap

end DifferentialGeometry.Analysis.Spectral
