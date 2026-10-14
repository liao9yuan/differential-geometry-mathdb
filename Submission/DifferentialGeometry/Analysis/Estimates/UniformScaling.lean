import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem exists_scaling_of_uniform_quad_bound
    {α : Type*} {P Q : ℝ → α → ℝ} {s₀ T : ℝ}
    (hQ : ∀ s x, 0 ≤ Q s x)
    (h : ∀ ε : ℝ, 0 < ε → ∃ d ∈ _root_.Set.Ioo s₀ T, ∀ s ∈ _root_.Set.Ioo d T, ∀ x,
      |P s x - Q s x| ≤ ε * Q s x) :
    ∃ s₁ ∈ _root_.Set.Ioo s₀ T, ∃ ell : ℝ → ℝ, (∀ s ∈ _root_.Set.Ioo s₁ T, 1 ≤ ell s) ∧
      Filter.Tendsto ell (𝓝[<] T) (𝓝 1) ∧
      ∀ s ∈ _root_.Set.Ioo s₁ T, ∀ x, P s x ≤ (ell s) ^ 2 * Q s x := by
  classical
  obtain ⟨s₁, hs₁, hbound⟩ := h 1 one_pos
  let S : ℝ → Set ℝ := fun s => {ε : ℝ | 0 ≤ ε ∧ ∀ x, |P s x - Q s x| ≤ ε * Q s x}
  have hne : ∀ s ∈ _root_.Set.Ioo s₁ T, (S s).Nonempty := fun s hs => ⟨1, zero_le_one, hbound s hs⟩
  have hell : ∀ s ∈ _root_.Set.Ioo s₁ T, 1 ≤ 1 + _root_.InfSet.sInf (S s) := by
    intro s hs
    have h0 : 0 ≤ _root_.InfSet.sInf (S s) := le_csInf (hne s hs) fun b hb => hb.1
    linarith
  have hquad : ∀ s ∈ _root_.Set.Ioo s₁ T, ∀ x, P s x ≤ (1 + _root_.InfSet.sInf (S s)) ^ 2 * Q s x := by
    intro s hs x
    have hsinf0 : 0 ≤ _root_.InfSet.sInf (S s) := le_csInf (hne s hs) fun b hb => hb.1
    have hmem : ∀ b ∈ S s, |P s x - Q s x| ≤ b * Q s x := fun b hb => hb.2 x
    have hhalf : P s x - Q s x ≤ _root_.InfSet.sInf (S s) * Q s x := by
      rcases eq_or_lt_of_le (hQ s x) with hzero | hpos
      · have hQ0 : Q s x = 0 := hzero.symm
        have hb1 := hmem 1 (show (1 : ℝ) ∈ S s from ⟨zero_le_one, hbound s hs⟩)
        simp only [hQ0, sub_zero, _root_.MulZeroClass.mul_zero] at hb1
        have hP0 : P s x = 0 := by
          have := abs_le.mp hb1
          linarith [this.1, this.2]
        simp [hP0, hQ0]
      · have hdiv : (P s x - Q s x) / Q s x ≤ _root_.InfSet.sInf (S s) := by
          refine le_csInf (hne s hs) fun b hb => ?_
          rw [div_le_iff₀ hpos]
          exact (abs_le.mp (hmem b hb)).2
        calc P s x - Q s x = ((P s x - Q s x) / Q s x) * Q s x := by field_simp
          _ ≤ _root_.InfSet.sInf (S s) * Q s x := mul_le_mul_of_nonneg_right hdiv (hQ s x)
    have hle2 : (1 + _root_.InfSet.sInf (S s)) ≤ (1 + _root_.InfSet.sInf (S s)) ^ 2 := by nlinarith [hsinf0]
    calc P s x = (P s x - Q s x) + Q s x := by ring
      _ ≤ _root_.InfSet.sInf (S s) * Q s x + Q s x := by linarith
      _ = (1 + _root_.InfSet.sInf (S s)) * Q s x := by ring
      _ ≤ (1 + _root_.InfSet.sInf (S s)) ^ 2 * Q s x := mul_le_mul_of_nonneg_right hle2 (hQ s x)
  have htend : Filter.Tendsto (fun s => 1 + _root_.InfSet.sInf (S s)) (𝓝[<] T) (𝓝 1) := by
    have hmain : Filter.Tendsto (fun s => _root_.InfSet.sInf (S s)) (𝓝[<] T) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨d, hd, hdb⟩ := h (ε / 2) (by linarith)
      filter_upwards [Ioo_mem_nhdsLT (show d < T from hd.2)] with s hs
      have hlow : 0 ≤ _root_.InfSet.sInf (S s) := le_csInf ⟨ε / 2, by linarith, hdb s hs⟩ fun b hb => hb.1
      have hup : _root_.InfSet.sInf (S s) ≤ ε / 2 :=
        csInf_le ⟨0, fun b hb => hb.1⟩ (show ε / 2 ∈ S s from ⟨by linarith, hdb s hs⟩)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hlow]
      linarith
    have := hmain.const_add (1 : ℝ)
    simpa using this
  exact ⟨s₁, hs₁, fun s => 1 + _root_.InfSet.sInf (S s), hell, htend, hquad⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_scaling_of_uniform_quad_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_scaling_of_uniform_quad_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_scaling_of_uniform_quad_bound ``Submission.DifferentialGeometry.Analysis.exists_scaling_of_uniform_quad_bound

end DifferentialGeometry.Analysis
