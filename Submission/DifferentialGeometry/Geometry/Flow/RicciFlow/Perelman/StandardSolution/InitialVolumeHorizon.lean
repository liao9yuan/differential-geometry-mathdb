import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVolumeLower

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.PDE.RicciFlow

theorem initialReducedVolumeLowerCoeff_antitoneOn (n : ℕ) (K c : ℝ)
    (hK : 0 < K) (hc : 0 < c) :
    AntitoneOn (fun H : ℝ ↦ initialReducedVolumeLowerCoeff n H K c) (_root_.Set.Ioi 0) := by
  have hr : 0 ≤ _root_.Min.min (c / 2) (intrinsicNormalMetricRadius n K) :=
    (lt_min (half_pos hc) (intrinsicNormalMetricRadius_pos n K hK.le)).le
  intro H₁ hH₁ H₂ _hH₂ hH
  change 0 < H₁ at hH₁
  have hG : (4 * Real.pi * H₂) ^ (-(n : ℝ) / 2) ≤
      (4 * Real.pi * H₁) ^ (-(n : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 4 * Real.pi * H₁)
      (mul_le_mul_of_nonneg_left hH (by positivity))
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
  unfold initialReducedVolumeLowerCoeff
  apply mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_left ?_ (intrinsicBallVolumeCoeff_pos n).le
  apply min_le_min ?_ le_rfl
  exact mul_le_mul_of_nonneg_left hG (pow_nonneg hr n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.initialReducedVolumeLowerCoeff_antitoneOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.initialReducedVolumeLowerCoeff_antitoneOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.initialReducedVolumeLowerCoeff_antitoneOn ``Submission.DifferentialGeometry.PDE.RicciFlow.initialReducedVolumeLowerCoeff_antitoneOn

end DifferentialGeometry.PDE.RicciFlow
end
