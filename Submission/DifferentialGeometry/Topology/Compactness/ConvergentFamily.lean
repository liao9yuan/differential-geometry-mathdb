import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.Filter
open scoped _root_.Topology

variable {X ι : Type*} [TopologicalSpace X]

theorem isCompact_insert_iUnion_of_eventually_subset {K : ι → Set X} {q : X}
    (hK : ∀ i, IsCompact (K i))
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ i in _root_.Filter.cofinite, K i ⊆ U) :
    IsCompact (_root_.Insert.insert q (⋃ i, K i)) := by
  classical
  apply isCompact_iff_finite_subcover.mpr
  intro J U hU hcover
  obtain ⟨j, hqj⟩ := mem_iUnion.mp (hcover (_root_.Set.mem_insert q _))
  have hfin : {i | ¬ K i ⊆ U j}.Finite := hlim (U j) ((hU j).mem_nhds hqj)
  have hcompact : IsCompact (⋃ i ∈ {i | ¬ K i ⊆ U j}, K i) :=
    hfin.isCompact_biUnion (fun i _ => hK i)
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U hU (by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxi⟩ := mem_iUnion.mp hi
    exact hcover (_root_.Set.mem_insert_of_mem _ (mem_iUnion.mpr ⟨i, hxi⟩)))
  refine ⟨insert j s, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hqj⟩⟩
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    by_cases hi : K i ⊆ U j
    · exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_insert_self _ _, hi hxi⟩⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.mp (hs (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hxi⟩⟩))
      obtain ⟨hks, hxk⟩ := mem_iUnion.mp hk
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hks, hxk⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `isCompact_insert_iUnion_of_eventually_subset then
    throwError "Refusing to shadow existing declaration isCompact_insert_iUnion_of_eventually_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `isCompact_insert_iUnion_of_eventually_subset ``Submission.isCompact_insert_iUnion_of_eventually_subset

theorem insert_iUnion_nat_add_mem_nhds
    {X : Type*} [TopologicalSpace X] {K : ℕ → Set X} {q : X}
    (hK : ∀ n, IsClosed (K n)) (hq : ∀ n, q ∉ K n)
    (hnhds : _root_.Insert.insert q (⋃ n, K n) ∈ 𝓝 q) (N : ℕ) :
    insert q (⋃ n, K (n + N)) ∈ 𝓝 q := by
  induction N with
  | zero => simpa only [Nat.add_zero] using hnhds
  | succ N ih =>
    filter_upwards [ih, (hK N).isOpen_compl.mem_nhds (hq N)] with x hx hnot
    rcases hx with rfl | hx
    · exact _root_.Set.mem_insert _ _
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      cases n with
      | zero => exact False.elim (hnot (by simpa only [Nat.zero_add] using hn))
      | succ n =>
        exact _root_.Set.mem_insert_of_mem _ (mem_iUnion.mpr ⟨n, by simpa only [Nat.succ_add, Nat.add_succ] using hn⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `insert_iUnion_nat_add_mem_nhds then
    throwError "Refusing to shadow existing declaration insert_iUnion_nat_add_mem_nhds"
  Lean.modifyEnv fun env => Lean.addAlias env `insert_iUnion_nat_add_mem_nhds ``Submission.insert_iUnion_nat_add_mem_nhds

theorem eventually_insert_iUnion_nat_add_subset
    {X : Type*} [TopologicalSpace X] {K : ℕ → Set X} {q : X}
    (hlim : ∀ U ∈ 𝓝 q, ∀ᶠ n in _root_.Filter.atTop, K n ⊆ U) {U : Set X} (hU : U ∈ 𝓝 q) :
    ∀ᶠ N in _root_.Filter.atTop, _root_.Insert.insert q (⋃ n, K (n + N)) ⊆ U := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim U hU)
  apply eventually_atTop.mpr
  refine ⟨N, fun n hn x hx => ?_⟩
  rcases hx with rfl | hx
  · exact mem_of_mem_nhds hU
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact hN (k + n) (hn.trans (Nat.le_add_left _ _)) hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `eventually_insert_iUnion_nat_add_subset then
    throwError "Refusing to shadow existing declaration eventually_insert_iUnion_nat_add_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `eventually_insert_iUnion_nat_add_subset ``Submission.eventually_insert_iUnion_nat_add_subset
