import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_normalize {f : ℝ → E} {f' : E} {x : ℝ}
    (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => NormedSpace.normalize (f y))
      (‖f x‖⁻¹ • f' - (⟪f x, f'⟫_ℝ / ‖f x‖ ^ 3) • f x) x := by
  have hn : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hd : HasDerivAt (fun y => ‖f y‖) (⟪f x, f'⟫_ℝ / ‖f x‖) x := by
    convert hf.norm_sq.sqrt (pow_ne_zero 2 hn) using 1
    · funext y
      exact (Real.sqrt_sq (norm_nonneg (f y))).symm
    · rw [Real.sqrt_sq (norm_nonneg _), mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hc : -(⟪f x, f'⟫_ℝ / ‖f x‖) / ‖f x‖ ^ 2 = -(⟪f x, f'⟫_ℝ / ‖f x‖ ^ 3) := by
    field_simp
  have h := (hd.inv hn).smul hf
  change HasDerivAt (fun y => ‖f y‖⁻¹ • f y)
    (‖f x‖⁻¹ • f' + (-(⟪f x, f'⟫_ℝ / ‖f x‖) / ‖f x‖ ^ 2) • f x) x at h
  simpa only [NormedSpace.normalize, hc, neg_smul, sub_eq_add_neg] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_normalize then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_normalize"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_normalize ``Submission.DifferentialGeometry.Analysis.hasDerivAt_normalize

theorem norm_deriv_normalize_le {f : ℝ → E} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    ‖deriv (fun y => NormedSpace.normalize (f y)) x‖ ≤ ‖deriv f x‖ / ‖f x‖ := by
  rw [(hasDerivAt_normalize hf.hasDerivAt hx).deriv]
  have hn : 0 < ‖f x‖ := norm_pos_iff.mpr hx
  have heq : ‖‖f x‖⁻¹ • deriv f x -
      (⟪f x, deriv f x⟫_ℝ / ‖f x‖ ^ 3) • f x‖ ^ 2 =
      (‖deriv f x‖ / ‖f x‖) ^ 2 - ⟪f x, deriv f x⟫_ℝ ^ 2 / ‖f x‖ ^ 4 := by
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
      real_inner_smul_right, real_inner_comm (deriv f x) (f x)]
    field_simp
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) hn.le)).mp
  rw [heq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (pow_nonneg hn.le _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_deriv_normalize_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_deriv_normalize_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_deriv_normalize_le ``Submission.DifferentialGeometry.Analysis.norm_deriv_normalize_le

end DifferentialGeometry.Analysis
