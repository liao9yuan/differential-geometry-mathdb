import Mathlib.Data.Set.Countable
import Mathlib.Data.Nat.Pairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace Countable
open _root_.Countable

open _root_.Countable in
theorem exists_sequence_strictMono_fibers (ι : Sort*) [Countable ι] [Nonempty ι] :
    ∃ f : ℕ → ι, ∀ i, ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n, f (s n) = i := by
  obtain ⟨g, hg⟩ := exists_surjective_nat ι
  refine ⟨fun n => g (Nat.unpair n).1, ?_⟩
  intro i
  obtain ⟨k, hk⟩ := hg i
  refine ⟨Nat.pair k, fun _ _ h => Nat.pair_lt_pair_right k h, ?_⟩
  intro n
  simpa only [Nat.unpair_pair] using hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Countable.exists_sequence_strictMono_fibers then
    throwError "Refusing to shadow existing declaration Countable.exists_sequence_strictMono_fibers"
  Lean.modifyEnv fun env => Lean.addAlias env `Countable.exists_sequence_strictMono_fibers ``Submission.Countable.exists_sequence_strictMono_fibers

open _root_.Countable in
theorem exists_sequence_cofinal_fibers (ι : Sort*) [Countable ι] [Nonempty ι] :
    ∃ f : ℕ → ι, ∀ i N, ∃ n, N ≤ n ∧ f n = i := by
  obtain ⟨f, hf⟩ := exists_sequence_strictMono_fibers ι
  refine ⟨f, ?_⟩
  intro i N
  obtain ⟨s, hs, heq⟩ := hf i
  exact ⟨s N, hs.id_le N, heq N⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Countable.exists_sequence_cofinal_fibers then
    throwError "Refusing to shadow existing declaration Countable.exists_sequence_cofinal_fibers"
  Lean.modifyEnv fun env => Lean.addAlias env `Countable.exists_sequence_cofinal_fibers ``Submission.Countable.exists_sequence_cofinal_fibers

end Countable

open _root_.Set _root_.Set.Countable in
theorem Set.Countable.exists_sequence_cofinal_fibers {α : Type*} {s : Set α}
    (hs : s.Countable) (hne : s.Nonempty) :
    ∃ f : ℕ → α, Set.range f = s ∧ ∀ i ∈ s, ∀ N, ∃ n, N ≤ n ∧ f n = i := by
  let _ : Countable s := hs.to_subtype
  let _ : Nonempty s := hne.to_subtype
  obtain ⟨f, hf⟩ := _root_.Submission.Countable.exists_sequence_cofinal_fibers s
  refine ⟨fun n => (f n).val, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro i ⟨n, rfl⟩
      exact (f n).property
    · intro i hi
      obtain ⟨n, _, hn⟩ := hf ⟨i, hi⟩ 0
      exact ⟨n, congrArg Subtype.val hn⟩
  · intro i hi N
    obtain ⟨n, hN, hn⟩ := hf ⟨i, hi⟩ N
    exact ⟨n, hN, congrArg Subtype.val hn⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Set
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Set.Countable
  let env ← Lean.getEnv
  if env.contains `Set.Countable.exists_sequence_cofinal_fibers then
    throwError "Refusing to shadow existing declaration Set.Countable.exists_sequence_cofinal_fibers"
  Lean.modifyEnv fun env => Lean.addAlias env `Set.Countable.exists_sequence_cofinal_fibers ``Submission.Set.Countable.exists_sequence_cofinal_fibers
