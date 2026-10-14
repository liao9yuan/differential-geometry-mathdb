import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Cofinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry

theorem exists_rescaling_factor_normalization {R Rl s τ : ℕ → ℝ} (hpos : ∀ n, 0 < Rl n)
    (hRl : _root_.Filter.Tendsto Rl _root_.Filter.atTop _root_.Filter.atTop) (hclose : ∀ n, |R n - Rl n| ≤ Rl n / 2)
    (hτs : ∀ n, τ n < s n) (hgap : ∀ n, (s n - τ n) * Rl n ≤ 1 / ((n : ℝ) + 1)) :
    (∀ n, 0 < R n) ∧ _root_.Filter.Tendsto R _root_.Filter.atTop _root_.Filter.atTop ∧ (∀ c : ℝ, ∃ C : ℝ, ∀ n, c ≤ C * R n) ∧
      Tendsto (fun n => R n * (τ n - s n)) _root_.Filter.atTop (𝓝 0) := by
  have hlow (n : ℕ) : Rl n / 2 ≤ R n := by
    have h := (abs_le.mp (hclose n)).1
    linarith
  have hup (n : ℕ) : R n ≤ 3 * Rl n / 2 := by
    have h := (abs_le.mp (hclose n)).2
    linarith
  have hRpos (n : ℕ) : 0 < R n := (half_pos (hpos n)).trans_le (hlow n)
  refine ⟨hRpos, _root_.Filter.tendsto_atTop_mono hlow (hRl.atTop_div_const two_pos), fun c => ?_, ?_⟩
  · have hcof : _root_.Filter.Tendsto R _root_.Filter.cofinite atTop := by
      rw [Nat.cofinite_eq_atTop]
      exact _root_.Filter.tendsto_atTop_mono hlow (hRl.atTop_div_const two_pos)
    obtain ⟨m, hm⟩ := hcof.exists_forall_le
    refine ⟨max c 0 / R m, fun n => ?_⟩
    have h1 : _root_.Max.max c 0 / R m * R m ≤ _root_.Max.max c 0 / R m * R n :=
      mul_le_mul_of_nonneg_left (hm n) (div_nonneg (le_max_right _ _) (hRpos m).le)
    rw [div_mul_cancel₀ _ (hRpos m).ne'] at h1
    exact (le_max_left _ _).trans h1
  · have hlim : _root_.Filter.Tendsto (fun n : ℕ => 3 / 2 * (1 / ((n : ℝ) + 1))) _root_.Filter.atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3 / 2 : ℝ)
    have hneg : _root_.Filter.Tendsto (fun n : ℕ => -(3 / 2 * (1 / ((n : ℝ) + 1)))) _root_.Filter.atTop (𝓝 0) := by
      simpa using hlim.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hneg tendsto_const_nhds (fun n => ?_)
      (fun n => ?_)
    · have hg : 0 < s n - τ n := sub_pos.mpr (hτs n)
      have h1 : R n * (s n - τ n) ≤ 3 * Rl n / 2 * (s n - τ n) :=
        mul_le_mul_of_nonneg_right (hup n) hg.le
      have h2 : 3 / 2 * ((s n - τ n) * Rl n) ≤ 3 / 2 * (1 / ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hgap n) (by norm_num)
      change -(3 / 2 * (1 / ((n : ℝ) + 1))) ≤ R n * (τ n - s n)
      nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos (hRpos n).le (sub_nonpos.mpr (hτs n).le)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_rescaling_factor_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_rescaling_factor_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_rescaling_factor_normalization ``Submission.DifferentialGeometry.exists_rescaling_factor_normalization

end DifferentialGeometry
