import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Order.Filter.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false

namespace EMetric

open _root_.Filter

theorem eq_true_self_of_eventually_edist_lt_or_ge
    {ι α : Type*} {M : α → Type*} [∀ k, PseudoEMetricSpace (M k)]
    (x : ι → ∀ k, M k) {l : Filter α} [l.NeBot]
    {r : ENNReal} (hr : 0 < r) (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in l,
      (near i j = _root_.Bool.true → _root_.EDist.edist (x i k) (x j k) < r) ∧
      (near i j = _root_.Bool.false → r ≤ _root_.EDist.edist (x i k) (x j k)))
    (i : ι) : near i i = true := by
  cases h : near i i
  · obtain ⟨k, hk⟩ := (hclass i i).exists
    have hzero := hk.2 h
    rw [_root_.PseudoEMetricSpace.edist_self] at hzero
    exact False.elim (not_le_of_gt hr hzero)
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.eq_true_self_of_eventually_edist_lt_or_ge then
    throwError "Refusing to shadow existing declaration EMetric.eq_true_self_of_eventually_edist_lt_or_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.eq_true_self_of_eventually_edist_lt_or_ge ``Submission.EMetric.eq_true_self_of_eventually_edist_lt_or_ge

theorem eq_swap_of_eventually_edist_lt_or_ge
    {ι α : Type*} {M : α → Type*} [∀ k, PseudoEMetricSpace (M k)]
    (x : ι → ∀ k, M k) {l : Filter α} [l.NeBot]
    {r : ENNReal} (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in l,
      (near i j = _root_.Bool.true → _root_.EDist.edist (x i k) (x j k) < r) ∧
      (near i j = _root_.Bool.false → r ≤ _root_.EDist.edist (x i k) (x j k)))
    (i j : ι) : near i j = near j i := by
  obtain ⟨k, hk, hk'⟩ := ((hclass i j).and (hclass j i)).exists
  cases hij : near i j <;> cases hji : near j i
  · rfl
  · have h := hk'.1 hji
    rw [_root_.PseudoEMetricSpace.edist_comm] at h
    exact False.elim (not_le_of_gt h (hk.2 hij))
  · have h := hk'.2 hji
    rw [_root_.PseudoEMetricSpace.edist_comm] at h
    exact False.elim (not_le_of_gt (hk.1 hij) h)
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `EMetric.eq_swap_of_eventually_edist_lt_or_ge then
    throwError "Refusing to shadow existing declaration EMetric.eq_swap_of_eventually_edist_lt_or_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `EMetric.eq_swap_of_eventually_edist_lt_or_ge ``Submission.EMetric.eq_swap_of_eventually_edist_lt_or_ge

end EMetric


end
