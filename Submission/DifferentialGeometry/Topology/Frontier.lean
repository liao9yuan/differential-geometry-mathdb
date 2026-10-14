import Submission.DifferentialGeometry.Topology.Combinatorics.BranchUpdates
import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open _root_.Set

theorem frontier_union_eq_sdiff_closure_of_frontier_subset_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = frontier A \ closure B := by
  apply Subset.antisymm
  · intro x hx
    have hxA : x ∈ frontier A := by
      rcases frontier_union_subset A B hx with hA | hB'
      · exact hA.1
      · exact False.elim (hx.2 (interior_mono _root_.Set.subset_union_left (hB hB'.2)))
    refine ⟨hxA, ?_⟩
    intro hxB
    apply hxA.2 (hB ⟨hxB, ?_⟩)
    intro hxBi
    exact hx.2 (interior_mono _root_.Set.subset_union_right hxBi)
  · rintro x ⟨hxA, hxB⟩
    refine ⟨closure_mono _root_.Set.subset_union_left hxA.1, ?_⟩
    intro hx
    apply hxA.2
    apply mem_interior.mpr
    refine ⟨interior (A ∪ B) ∩ (closure B)ᶜ, ?_,
      isOpen_interior.inter isClosed_closure.isOpen_compl, hx, hxB⟩
    intro y hy
    exact (interior_subset hy.1).resolve_right (fun h ↦ hy.2 (subset_closure h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.frontier_union_eq_sdiff_closure_of_frontier_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.frontier_union_eq_sdiff_closure_of_frontier_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.frontier_union_eq_sdiff_closure_of_frontier_subset_interior ``Submission.DifferentialGeometry.Topology.frontier_union_eq_sdiff_closure_of_frontier_subset_interior

theorem frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hclosed : IsClosed B) (hB : frontier B ⊆ interior A) :
    frontier (A ∪ B) = frontier A \ B := by
  rw [frontier_union_eq_sdiff_closure_of_frontier_subset_interior hB, hclosed.closure_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior ``Submission.DifferentialGeometry.Topology.frontier_union_eq_sdiff_of_isClosed_of_frontier_subset_interior

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

theorem isOpen_iUnion_of_recurrent_frontier_updates
    {M ι : Type*} [TopologicalSpace M]
    (W : ℕ → Set M) (face : ℕ → ι → Set M) (label : ℕ → ι)
    (hfrontier : ∀ n, frontier (W n) ⊆ ⋃ i, face n i)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (hrecurrent : ∀ i N, ∃ n, N ≤ n ∧ label n = i) :
    IsOpen (⋃ n, W n) := by
  classical
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  have hxi : ∃ k, x ∈ interior (W k) := by
    by_cases hint : x ∈ interior (W n)
    · exact ⟨n, hint⟩
    have hxf : x ∈ frontier (W n) := (mem_frontier_iff_notMem_interior hxn).mpr hint
    obtain ⟨i, hface⟩ := Set.mem_iUnion.mp (hfrontier n hxf)
    have hex : ∃ k, n ≤ k ∧ label k = i := hrecurrent i n
    have hk := Nat.find_spec hex
    have heq : face (Nat.find hex) i = face n i :=
      eq_of_no_update_between label face hunchanged i hk.1 (by
        intro m hnm hmk hm
        exact Nat.find_min hex hmk ⟨hnm, hm⟩)
    refine ⟨Nat.find hex + 1, hfilled _ ?_⟩
    rw [hk.2, heq]
    exact hface
  obtain ⟨k, hk⟩ := hxi
  exact ⟨interior (W k), interior_subset.trans (Set.subset_iUnion W k), isOpen_interior, hk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOpen_iUnion_of_recurrent_frontier_updates then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOpen_iUnion_of_recurrent_frontier_updates"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOpen_iUnion_of_recurrent_frontier_updates ``Submission.DifferentialGeometry.Topology.isOpen_iUnion_of_recurrent_frontier_updates

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open _root_.Set

theorem closure_interior_eq_of_frontier_subset_closure_interior
    {M : Type*} [TopologicalSpace M] {D : Set M} (hD : IsClosed D)
    (hfront : frontier D ⊆ closure (interior D)) : closure (interior D) = D := by
  apply Subset.antisymm hD.closure_interior_subset
  intro x hx
  by_cases hi : x ∈ interior D
  · exact subset_closure hi
  · exact hfront ((mem_frontier_iff_notMem_interior hx).mpr hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closure_interior_eq_of_frontier_subset_closure_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closure_interior_eq_of_frontier_subset_closure_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closure_interior_eq_of_frontier_subset_closure_interior ``Submission.DifferentialGeometry.Topology.closure_interior_eq_of_frontier_subset_closure_interior

theorem eq_univ_of_recurrent_frontier_attachments
    {X Y ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [Finite ι]
    (R B : ℕ → Set X) (hclosed : IsClosed (R 0)) (hne : (R 0).Nonempty)
    (hstep : ∀ n, R (n + 1) = R n ∪ B n)
    (face : ℕ → ι → Set X) (label : ℕ → ι)
    (hfrontier : ∀ n, frontier (R n) ⊆ ⋃ i, face n i)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hfilled : ∀ n, face n (label n) ⊆ interior (R (n + 1)))
    (hrecurrent : ∀ i N, ∃ n, N ≤ n ∧ label n = i)
    (ends : ι → Y → X) (hclosedRanges : ∀ i, IsClosed (_root_.Set.range (ends i)))
    (hrange : ∀ i, _root_.Set.range (ends i) = ⋃ n, ⋃ (_ : label n = i), B n) :
    (⋃ n, R n) = _root_.Set.univ ∧ R 0 ∪ ⋃ i, _root_.Set.range (ends i) = univ := by
  have hdecomposition : (⋃ n, R n) = R 0 ∪ ⋃ i, _root_.Set.range (ends i) := by
    apply Subset.antisymm
    · apply _root_.Set.iUnion_subset
      intro n
      induction n with
      | zero => exact _root_.Set.subset_union_left
      | succ n ih =>
        rw [hstep n]
        refine _root_.Set.union_subset ih ?_
        intro x hx
        right
        apply mem_iUnion.mpr
        refine ⟨label n, ?_⟩
        rw [hrange]
        exact mem_iUnion₂.mpr ⟨n, rfl, hx⟩
    · refine _root_.Set.union_subset (_root_.Set.subset_iUnion R 0) ?_
      apply _root_.Set.iUnion_subset
      intro i
      rw [hrange]
      apply _root_.Set.iUnion_subset
      intro n
      apply _root_.Set.iUnion_subset
      intro hn
      have hsub : B n ⊆ R (n + 1) := (hstep n).symm ▸ _root_.Set.subset_union_right
      exact hsub.trans (_root_.Set.subset_iUnion R (n + 1))
  have hopen : IsOpen (⋃ n, R n) :=
    isOpen_iUnion_of_recurrent_frontier_updates R face label hfrontier hunchanged hfilled hrecurrent
  have hclosedall : IsClosed (⋃ n, R n) := by
    rw [hdecomposition]
    exact hclosed.union (isClosed_iUnion_of_finite hclosedRanges)
  have hfull : (⋃ n, R n) = univ :=
    (show IsClopen (⋃ n, R n) from ⟨hclosedall, hopen⟩).eq_univ
      (hne.mono (_root_.Set.subset_iUnion R 0))
  exact ⟨hfull, hdecomposition.symm.trans hfull⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments ``Submission.DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments

theorem eq_univ_of_recurrent_frontier_attachments_of_proper
    {X Y ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [Finite ι]
    (R B : ℕ → Set X) (hclosed : IsClosed (R 0)) (hne : (R 0).Nonempty)
    (hstep : ∀ n, R (n + 1) = R n ∪ B n)
    (face : ℕ → ι → Set X) (label : ℕ → ι)
    (hfrontier : ∀ n, frontier (R n) ⊆ ⋃ i, face n i)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hfilled : ∀ n, face n (label n) ⊆ interior (R (n + 1)))
    (hrecurrent : ∀ i N, ∃ n, N ≤ n ∧ label n = i)
    (ends : ι → Y → X) (hproper : ∀ i, IsProperMap (ends i))
    (hrange : ∀ i, _root_.Set.range (ends i) = ⋃ n, ⋃ (_ : label n = i), B n) :
    (⋃ n, R n) = _root_.Set.univ ∧ R 0 ∪ ⋃ i, _root_.Set.range (ends i) = univ  := by
  exact eq_univ_of_recurrent_frontier_attachments R B hclosed hne hstep face label
    hfrontier hunchanged hfilled hrecurrent ends (fun i => (hproper i).isClosed_range) hrange

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments_of_proper then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments_of_proper"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments_of_proper ``Submission.DifferentialGeometry.Topology.eq_univ_of_recurrent_frontier_attachments_of_proper

end DifferentialGeometry.Topology
