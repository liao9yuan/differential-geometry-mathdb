import Mathlib.Analysis.Convex.Segment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

theorem linear_interpolation_signs_eq_of_ne_zero
    {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {a b : 𝕜}
    (hn : ∀ t ∈ _root_.Set.Icc (0 : 𝕜) 1, (1 - t) * a + t * b ≠ 0) :
    (a ≤ 0 ↔ b ≤ 0) ∧ (a < 0 ↔ b < 0) ∧ (a = 0 ↔ b = 0) := by
  have hnot : (0 : 𝕜) ∉ _root_.Set.uIcc a b := by
    rw [← segment_eq_uIcc, segment_eq_image]
    rintro ⟨t, ht, hz⟩
    exact hn t ht (by simpa only [smul_eq_mul] using hz)
  have hs : (a < 0 ∧ b < 0) ∨ (0 < a ∧ 0 < b) := by
    by_cases hmax : _root_.Max.max a b < 0
    · exact Or.inl ⟨(le_max_left a b).trans_lt hmax, (le_max_right a b).trans_lt hmax⟩
    · have hmin : 0 < _root_.Min.min a b := lt_of_not_ge
        (fun h => hnot ⟨h, le_of_not_gt hmax⟩)
      exact Or.inr ⟨hmin.trans_le (min_le_left a b), hmin.trans_le (min_le_right a b)⟩
  rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨iff_of_true ha.le hb.le, iff_of_true ha hb, iff_of_false ha.ne hb.ne⟩
  · exact ⟨iff_of_false (not_le_of_gt ha) (not_le_of_gt hb),
      iff_of_false (not_lt_of_ge ha.le) (not_lt_of_ge hb.le), iff_of_false ha.ne' hb.ne'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `linear_interpolation_signs_eq_of_ne_zero then
    throwError "Refusing to shadow existing declaration linear_interpolation_signs_eq_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `linear_interpolation_signs_eq_of_ne_zero ``Submission.linear_interpolation_signs_eq_of_ne_zero
