import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

open _root_.Set _root_.Set.Finite in
theorem Set.Finite.exists_strictMono_enumeration_fiber {I : Type*} {label : ℕ → I}
    (hfinite : (_root_.Set.range label).Finite) :
    ∃ i : I, ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ n, label (s n) = i) ∧
      (∀ m, label m = i ↔ ∃ n, s n = m) ∧
      (∀ m, label m = i → s 0 ≤ m) ∧
      ∀ n m, s n < m → m < s (n + 1) → label m ≠ i := by
  let _ : Finite (_root_.Set.range label) := hfinite.to_subtype
  obtain ⟨i, hi⟩ :=
    Finite.exists_infinite_fiber (fun n => (⟨label n, _root_.Set.mem_range_self n⟩ : _root_.Set.range label))
  have hinfinite : (Set.ofPred (fun m => label m = i.val)).Infinite := by
    have he : (fun n => (⟨label n, _root_.Set.mem_range_self n⟩ : _root_.Set.range label)) ⁻¹' {i} =
        Set.ofPred (fun m => label m = i.val) := by
      ext m
      simp only [_root_.Set.mem_preimage, _root_.Set.mem_singleton_iff, Subtype.ext_iff, _root_.Set.mem_ofPred]
    rw [← he]
    exact Set.infinite_coe_iff.mp hi
  let s := Nat.nth (fun m => label m = i.val)
  have hmono : StrictMono s := Nat.nth_strictMono hinfinite
  have hmem (n : ℕ) : label (s n) = i.val := Nat.nth_mem_of_infinite hinfinite n
  have hcover (m : ℕ) : label m = i.val ↔ ∃ n, s n = m := by
    change m ∈ Set.ofPred (fun m => label m = i.val) ↔ m ∈ _root_.Set.range s
    rw [Nat.range_nth_of_infinite hinfinite]
  refine ⟨i.val, s, hmono, hmem, hcover, ?_, ?_⟩
  · intro m hm
    obtain ⟨n, rfl⟩ := (hcover m).mp hm
    exact hmono.monotone (Nat.zero_le n)
  · intro n m hnm hms hm
    exact hnm.not_ge (Nat.le_nth_of_lt_nth_succ hms hm)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Set
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Set.Finite
  let env ← Lean.getEnv
  if env.contains `Set.Finite.exists_strictMono_enumeration_fiber then
    throwError "Refusing to shadow existing declaration Set.Finite.exists_strictMono_enumeration_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Set.Finite.exists_strictMono_enumeration_fiber ``Submission.Set.Finite.exists_strictMono_enumeration_fiber

open _root_.Finite in
theorem Finite.exists_strictMono_enumeration_fiber {I : Type*} [Finite I] (label : ℕ → I) :
    ∃ i : I, ∃ s : ℕ → ℕ, StrictMono s ∧
      (∀ n, label (s n) = i) ∧
      (∀ m, label m = i ↔ ∃ n, s n = m) ∧
      (∀ m, label m = i → s 0 ≤ m) ∧
      ∀ n m, s n < m → m < s (n + 1) → label m ≠ i :=
  (Set.toFinite (_root_.Set.range label)).exists_strictMono_enumeration_fiber

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Finite
  let env ← Lean.getEnv
  if env.contains `Finite.exists_strictMono_enumeration_fiber then
    throwError "Refusing to shadow existing declaration Finite.exists_strictMono_enumeration_fiber"
  Lean.modifyEnv fun env => Lean.addAlias env `Finite.exists_strictMono_enumeration_fiber ``Submission.Finite.exists_strictMono_enumeration_fiber
