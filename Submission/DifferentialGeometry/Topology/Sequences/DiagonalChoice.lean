import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Topology

namespace Filter
open _root_.Filter

open _root_.Filter in
theorem exists_seq_forall_of_eventually {α : Type*} {F : ℕ → Filter α} [∀ n, (F n).NeBot]
    {ι : ℕ → Type*} [∀ n, Finite (ι n)] {p : ∀ n, ι n → α → Prop}
    (h : ∀ n i, ∀ᶠ a in F n, p n i a) : ∃ a : ℕ → α, ∀ n i, p n i (a n) := by
  choose a ha using fun n => (_root_.Filter.eventually_all.2 (h n)).exists
  exact ⟨a, ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.exists_seq_forall_of_eventually then
    throwError "Refusing to shadow existing declaration Filter.exists_seq_forall_of_eventually"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.exists_seq_forall_of_eventually ``Submission.Filter.exists_seq_forall_of_eventually

open _root_.Filter in
theorem exists_seq_mem_Ioo_forall_of_eventually_nhdsLT {s b : ℕ → ℝ} (hb : ∀ n, b n < s n)
    {ι : ℕ → Type*} [∀ n, Finite (ι n)] {p : ∀ n, ι n → ℝ → Prop}
    (h : ∀ n i, ∀ᶠ τ in 𝓝[<] s n, p n i τ) :
    ∃ τ : ℕ → ℝ, (∀ n, τ n ∈ _root_.Set.Ioo (b n) (s n)) ∧ ∀ n i, p n i (τ n) := by
  choose τ hτ using fun n => (Eventually.and (Ioo_mem_nhdsLT (hb n))
    (_root_.Filter.eventually_all.2 (h n))).exists
  exact ⟨τ, fun n => (hτ n).1, fun n => (hτ n).2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT then
    throwError "Refusing to shadow existing declaration Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT"
  Lean.modifyEnv fun env => Lean.addAlias env `Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT ``Submission.Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT

end Filter
