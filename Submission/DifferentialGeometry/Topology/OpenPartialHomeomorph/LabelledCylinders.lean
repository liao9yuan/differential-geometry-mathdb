import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

variable {N T M : Type*} [TopologicalSpace N] [TopologicalSpace T] [PartialOrder T]
  [OrderTopology T] [TopologicalSpace M]

open _root_.OpenPartialHomeomorph in
theorem image_Icc_subset_interior_union_upper_boundary
    (e : OpenPartialHomeomorph (N × T) M) {a b : T} {W : Set M}
    (hsource : _root_.Set.univ ×ˢ _root_.Set.Icc a b ⊆ e.source)
    (hcontained : e '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) ⊆ W)
    (hlower : e '' (_root_.Set.univ ×ˢ ({a} : Set T)) ⊆ interior W) :
    e '' (_root_.Set.univ ×ˢ _root_.Set.Icc a b) ⊆ interior W ∪ e '' (_root_.Set.univ ×ˢ ({b} : Set T)) := by
  have hsub : (_root_.Set.univ : Set N) ×ˢ _root_.Set.Ioo a b ⊆ _root_.Set.univ ×ˢ _root_.Set.Icc a b :=
    _root_.Set.prod_mono_right _root_.Set.Ioo_subset_Icc_self
  have hopen : IsOpen (e '' (_root_.Set.univ ×ˢ _root_.Set.Ioo a b)) :=
    e.isOpen_image_of_subset_source (isOpen_univ.prod (isOpen_Ioo' a b)) (hsub.trans hsource)
  have hint : e '' (_root_.Set.univ ×ˢ _root_.Set.Ioo a b) ⊆ interior W :=
    interior_maximal ((_root_.Set.image_mono hsub).trans hcontained) hopen
  rintro y ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩
  rcases ht.1.eq_or_lt with h | h
  · exact Or.inl (hlower ⟨(z, t), ⟨mem_univ _, h.symm⟩, rfl⟩)
  · rcases ht.2.eq_or_lt with h' | h'
    · exact Or.inr ⟨(z, t), ⟨mem_univ _, h'⟩, rfl⟩
    · exact Or.inl (hint ⟨(z, t), ⟨mem_univ _, h, h'⟩, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.image_Icc_subset_interior_union_upper_boundary then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.image_Icc_subset_interior_union_upper_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.image_Icc_subset_interior_union_upper_boundary ``Submission.OpenPartialHomeomorph.image_Icc_subset_interior_union_upper_boundary

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology

private theorem disjoint_of_frontier_faces_at_max
    {M ι : Type*} [TopologicalSpace M]
    (label : ℕ → ι) (face : ℕ → ι → Set M) (band W : ℕ → Set M)
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (hW : Monotone W)
    (hcontained : ∀ n, band n ⊆ W (n + 1))
    (hinter : ∀ n, band n ∩ W n = face n (label n))
    (hfrontier : ∀ n, face n (label n) ⊆ frontier (W n))
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (hexposed : ∀ n, band n ⊆ interior (W (n + 1)) ∪ face (n + 1) (label n))
    (a b : ℕ) (hne : label a ≠ label b)
    (hdisjoint : Disjoint (face (_root_.Max.max a b) (label a)) (face (_root_.Max.max a b) (label b))) :
    Disjoint (band a) (band b) := by
  have hprop (a b : ℕ) (hab : a + 1 ≤ b) :
      band a ⊆ interior (W b) ∪ face b (label a) := by
    induction b, hab using Nat.le_induction with
    | base => exact hexposed a
    | succ b hab ih =>
      intro x hx
      rcases ih hx with hx | hx
      · exact Or.inl (interior_mono (hW (Nat.le_succ b)) hx)
      · by_cases hba : label b = label a
        · exact Or.inl (hfilled b (by simpa only [hba] using hx))
        · exact Or.inr ((hunchanged b (label a) hba).symm ▸ hx)
  have hlt (a b : ℕ) (hab : a < b)
      (hd : Disjoint (face b (label a)) (face b (label b))) :
      Disjoint (band a) (band b) := by
    apply disjoint_left.mpr
    intro x hxa hxb
    have hxW : x ∈ W b := hW (Nat.succ_le_of_lt hab) (hcontained a hxa)
    have hxbface : x ∈ face b (label b) := hinter b ▸ ⟨hxb, hxW⟩
    rcases hprop a b (Nat.succ_le_of_lt hab) hxa with hxint | hxface
    · exact (hfrontier b hxbface).2 hxint
    · exact disjoint_left.mp hd hxface hxbface
  rcases lt_trichotomy a b with hab | hab | hab
  · exact hlt a b hab (by simpa only [max_eq_right hab.le] using hdisjoint)
  · exact (hne (congrArg label hab)).elim
  · exact (hlt b a hab (by simpa only [max_eq_left hab.le] using hdisjoint.symm)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.disjoint_of_frontier_faces_at_max
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.disjoint_of_frontier_faces_at_max target :: scope.openDecls } }

end DifferentialGeometry.Topology

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

open _root_.Submission.DifferentialGeometry.Topology

open _root_.OpenPartialHomeomorph in
theorem disjoint_cylinder_images_of_disjoint_frontier_faces
    {N T M ι : Type*} [TopologicalSpace N] [TopologicalSpace T]
    [PartialOrder T] [OrderTopology T] [TopologicalSpace M] {c d : T}
    (label : ℕ → ι) (face : ℕ → ι → Set M)
    (P : ℕ → OpenPartialHomeomorph (N × T) M)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc c d ⊆ (P n).source)
    (hlower : ∀ n, P n '' (_root_.Set.univ ×ˢ ({c} : Set T)) ⊆ face n (label n))
    (hupper : ∀ n, P n '' (_root_.Set.univ ×ˢ ({d} : Set T)) ⊆ face (n + 1) (label n))
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d) ∩ W n = face n (label n))
    (hfrontier : ∀ n, face n (label n) ⊆ frontier (W n))
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (a b : ℕ) (hne : label a ≠ label b)
    (hdisjoint : Disjoint (face (_root_.Max.max a b) (label a)) (face (_root_.Max.max a b) (label b))) :
    Disjoint (P a '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d)) (P b '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d)) := by
  apply disjoint_of_frontier_faces_at_max label face
    (fun n => P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d)) W hunchanged hW hcontained
    hinter hfrontier hfilled _ a b hne hdisjoint
  intro n
  exact ((P n).image_Icc_subset_interior_union_upper_boundary (hsource n)
    (hcontained n) ((hlower n).trans (hfilled n))).trans (_root_.Set.union_subset_union_right _ (hupper n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.disjoint_cylinder_images_of_disjoint_frontier_faces then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.disjoint_cylinder_images_of_disjoint_frontier_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.disjoint_cylinder_images_of_disjoint_frontier_faces ``Submission.OpenPartialHomeomorph.disjoint_cylinder_images_of_disjoint_frontier_faces

open _root_.OpenPartialHomeomorph in
theorem disjoint_cylinder_images_of_distinct_labels
    {N T M ι : Type*} [TopologicalSpace N] [TopologicalSpace T]
    [PartialOrder T] [OrderTopology T] [TopologicalSpace M] {c d : T}
    (label : ℕ → ι) (face : ℕ → ι → Set M)
    (P : ℕ → OpenPartialHomeomorph (N × T) M)
    (hsource : ∀ n, _root_.Set.univ ×ˢ _root_.Set.Icc c d ⊆ (P n).source)
    (hlower : ∀ n, P n '' (_root_.Set.univ ×ˢ ({c} : Set T)) ⊆ face n (label n))
    (hupper : ∀ n, P n '' (_root_.Set.univ ×ˢ ({d} : Set T)) ⊆ face (n + 1) (label n))
    (hunchanged : ∀ n i, label n ≠ i → face (n + 1) i = face n i)
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d) ∩ W n = face n (label n))
    (hfrontier : ∀ n, face n (label n) ⊆ frontier (W n))
    (hfilled : ∀ n, face n (label n) ⊆ interior (W (n + 1)))
    (hdisjoint : ∀ n, (_root_.Set.range label).Pairwise (fun i j => Disjoint (face n i) (face n j)))
    (a b : ℕ) (hne : label a ≠ label b) :
    Disjoint (P a '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d)) (P b '' (_root_.Set.univ ×ˢ _root_.Set.Icc c d)) := by
  apply disjoint_cylinder_images_of_disjoint_frontier_faces label face P hsource hlower hupper
    hunchanged W hW hcontained hinter hfrontier hfilled a b hne
  exact hdisjoint (_root_.Max.max a b) (_root_.Set.mem_range_self a) (_root_.Set.mem_range_self b) hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.disjoint_cylinder_images_of_distinct_labels then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.disjoint_cylinder_images_of_distinct_labels"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.disjoint_cylinder_images_of_distinct_labels ``Submission.OpenPartialHomeomorph.disjoint_cylinder_images_of_distinct_labels

end OpenPartialHomeomorph
