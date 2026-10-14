import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Geometry.Affine

theorem exists_Icc_eq_preimage_affine (s c a b : ℝ) (hs : s ≠ 0) :
    ∃ l r : ℝ, (fun z ↦ s * z + c) ⁻¹' _root_.Set.Icc a b = _root_.Set.Icc l r ∧
      r - l = (b - a) / |s| := by
  have hpre : (fun z ↦ s * z + c) ⁻¹' _root_.Set.Icc a b =
      (fun z ↦ s * z) ⁻¹' _root_.Set.Icc (a - c) (b - c) := by
    ext z
    change (a ≤ s * z + c ∧ s * z + c ≤ b) ↔ (a - c ≤ s * z ∧ s * z ≤ b - c)
    constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
  rcases lt_or_gt_of_ne hs with hs | hs
  · refine ⟨(b - c) / s, (a - c) / s, ?_, ?_⟩
    · rw [hpre, _root_.Set.preimage_const_mul_Icc_of_neg _ _ hs]
    · rw [abs_of_neg hs]
      ring
  · refine ⟨(a - c) / s, (b - c) / s, ?_, ?_⟩
    · rw [hpre, _root_.Set.preimage_const_mul_Icc₀ _ _ hs]
    · rw [abs_of_pos hs]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Affine.exists_Icc_eq_preimage_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Affine.exists_Icc_eq_preimage_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Affine.exists_Icc_eq_preimage_affine ``Submission.DifferentialGeometry.Geometry.Affine.exists_Icc_eq_preimage_affine

theorem exists_Icc_of_comparable_scales
    (α β a b B σ c : ℝ) (hβ : 0 < β)
    (hscale : β ≤ 2 * α) (hwidth : 1 ≤ b - a) (herror : B ≤ α / 4)
    (hσ : σ = 1 ∨ σ = -1) :
    ∃ l r : ℝ, (fun z ↦ σ * (β * z) + c) ⁻¹' _root_.Set.Icc (α * a + B) (α * b - B) = _root_.Set.Icc l r ∧
      1 / 4 ≤ r - l := by
  have hα : 0 < α := by linarith only [hβ, hscale]
  have hs : σ * β ≠ 0 := by
    rcases hσ with rfl | rfl <;> simp [hβ.ne']
  obtain ⟨l, r, heq, hlen⟩ := exists_Icc_eq_preimage_affine (σ * β) c
    (α * a + B) (α * b - B) hs
  have habs : |σ * β| = β := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos hβ]
  refine ⟨l, r, ?_, ?_⟩
  · simpa only [mul_assoc] using heq
  · rw [hlen, habs]
    apply (le_div_iff₀ hβ).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hwidth hα.le, hscale, herror]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Affine.exists_Icc_of_comparable_scales then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Affine.exists_Icc_of_comparable_scales"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Affine.exists_Icc_of_comparable_scales ``Submission.DifferentialGeometry.Geometry.Affine.exists_Icc_of_comparable_scales

end DifferentialGeometry.Geometry.Affine
