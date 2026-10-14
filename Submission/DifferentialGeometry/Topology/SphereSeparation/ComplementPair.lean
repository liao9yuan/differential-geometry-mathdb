import Submission.DifferentialGeometry.Topology.SphereSeparation.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open _root_.Set

structure ComplementPair {X : Type*} [TopologicalSpace X] (S : Set X) where
  left : Set X
  right : Set X
  isOpen_left : IsOpen left
  isOpen_right : IsOpen right
  isConnected_left : IsConnected left
  isConnected_right : IsConnected right
  disjoint : Disjoint left right
  union_eq_compl : left ∪ right = Sᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair

namespace ComplementPair

variable {X : Type*} [TopologicalSpace X] {S C : Set X}

theorem left_subset_compl (p : ComplementPair S) : p.left ⊆ Sᶜ := by
  rw [← p.union_eq_compl]
  exact _root_.Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_subset_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_subset_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_subset_compl ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_subset_compl

theorem right_subset_compl (p : ComplementPair S) : p.right ⊆ Sᶜ := by
  rw [← p.union_eq_compl]
  exact _root_.Set.subset_union_right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_subset_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_subset_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_subset_compl ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_subset_compl

theorem left_disjoint_sphere (p : ComplementPair S) : Disjoint p.left S := by
  rw [Set.disjoint_left]
  exact fun _ hx hS => p.left_subset_compl hx hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_disjoint_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_disjoint_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_disjoint_sphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.left_disjoint_sphere

theorem right_disjoint_sphere (p : ComplementPair S) : Disjoint p.right S := by
  rw [Set.disjoint_left]
  exact fun _ hx hS => p.right_subset_compl hx hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_disjoint_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_disjoint_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_disjoint_sphere ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.right_disjoint_sphere

theorem subset_left_or_subset_right (p : ComplementPair S)
    (hC : IsPreconnected C) (hCS : C ⊆ Sᶜ) :
    C ⊆ p.left ∨ C ⊆ p.right := by
  apply hC.subset_or_subset p.isOpen_left p.isOpen_right p.disjoint
  simpa only [p.union_eq_compl] using hCS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.subset_left_or_subset_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.subset_left_or_subset_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.subset_left_or_subset_right ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.subset_left_or_subset_right

theorem not_mem_connectedComponentIn_of_left_of_right (p : ComplementPair S) {a z : X}
    (ha : a ∈ p.right) (hz : z ∈ p.left) : z ∉ connectedComponentIn Sᶜ a := by
  intro hzcomp
  have hacompl : a ∈ Sᶜ := p.right_subset_compl ha
  have hsub : connectedComponentIn Sᶜ a ⊆ Sᶜ := connectedComponentIn_subset Sᶜ a
  rcases p.subset_left_or_subset_right isPreconnected_connectedComponentIn hsub with h | h
  · exact Set.disjoint_left.mp p.disjoint (h (mem_connectedComponentIn hacompl)) ha
  · exact Set.disjoint_left.mp p.disjoint hz (h hzcomp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.not_mem_connectedComponentIn_of_left_of_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.not_mem_connectedComponentIn_of_left_of_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.not_mem_connectedComponentIn_of_left_of_right ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.not_mem_connectedComponentIn_of_left_of_right

theorem side_iff_of_isPreconnected_subset_compl (p : ComplementPair S) {C : Set X}
    (hC : IsPreconnected C) (hsub : C ⊆ Sᶜ) {a b : X} (ha : a ∈ C) (hb : b ∈ C) :
    (a ∈ p.left ↔ b ∈ p.left) ∧ (a ∈ p.right ↔ b ∈ p.right) := by
  rcases p.subset_left_or_subset_right hC hsub with h | h
  · exact ⟨iff_of_true (h ha) (h hb),
      iff_of_false
        (fun hx => Set.disjoint_left.mp p.disjoint (h ha) hx)
        (fun hx => Set.disjoint_left.mp p.disjoint (h hb) hx)⟩
  · exact ⟨iff_of_false
        (fun hx => Set.disjoint_left.mp p.disjoint hx (h ha))
        (fun hx => Set.disjoint_left.mp p.disjoint hx (h hb)),
      iff_of_true (h ha) (h hb)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.side_iff_of_isPreconnected_subset_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.side_iff_of_isPreconnected_subset_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.side_iff_of_isPreconnected_subset_compl ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.side_iff_of_isPreconnected_subset_compl

theorem closure_left_eq (p : ComplementPair S) (hSleft : S ⊆ closure p.left) :
    closure p.left = p.left ∪ S := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hxCompl : x ∈ Sᶜ := hxS
      rw [← p.union_eq_compl] at hxCompl
      rcases hxCompl with hxLeft | hxRight
      · exact Or.inl hxLeft
      · exact False.elim (Set.disjoint_left.1 (p.disjoint.closure_left p.isOpen_right) hx hxRight)
  · exact _root_.Set.union_subset subset_closure hSleft

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_left_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_left_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_left_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_left_eq


theorem closure_right_eq (p : ComplementPair S) (hSright : S ⊆ closure p.right) :
    closure p.right = p.right ∪ S := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxS : x ∈ S
    · exact Or.inr hxS
    · have hxCompl : x ∈ Sᶜ := hxS
      rw [← p.union_eq_compl] at hxCompl
      rcases hxCompl with hxLeft | hxRight
      · exact False.elim
          (Set.disjoint_left.1 (p.disjoint.closure_right p.isOpen_left) hxLeft hx)
      · exact Or.inl hxRight
  · exact _root_.Set.union_subset subset_closure hSright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_right_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_right_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_right_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.closure_right_eq

theorem frontier_left_eq (p : ComplementPair S) (hSleft : S ⊆ closure p.left) :
    frontier p.left = S := by
  rw [p.isOpen_left.frontier_eq, p.closure_left_eq hSleft]
  ext x
  constructor
  · rintro ⟨hx, hxNotLeft⟩
    rcases hx with hxLeft | hxS
    · exact False.elim (hxNotLeft hxLeft)
    · exact hxS
  · intro hxS
    exact ⟨Or.inr hxS, fun hxLeft =>
      Set.disjoint_left.1 p.left_disjoint_sphere hxLeft hxS⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_left_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_left_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_left_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_left_eq

theorem frontier_right_eq (p : ComplementPair S) (hSright : S ⊆ closure p.right) :
    frontier p.right = S := by
  rw [p.isOpen_right.frontier_eq, p.closure_right_eq hSright]
  ext x
  constructor
  · rintro ⟨hx, hxNotRight⟩
    rcases hx with hxRight | hxS
    · exact False.elim (hxNotRight hxRight)
    · exact hxS
  · intro hxS
    exact ⟨Or.inr hxS, fun hxRight =>
      Set.disjoint_left.1 p.right_disjoint_sphere hxRight hxS⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_right_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_right_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_right_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.frontier_right_eq

theorem interior_closure_left_eq (p : ComplementPair S)
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    interior (closure p.left) = p.left := by
  apply Set.Subset.antisymm
  · intro x hxInterior
    have hxClosure : x ∈ closure p.left := interior_subset hxInterior
    rw [p.closure_left_eq hSleft] at hxClosure
    rcases hxClosure with hxLeft | hxS
    · exact hxLeft
    · have hxRightClosure : x ∈ closure p.right := hSright hxS
      obtain ⟨y, hyInterior, hyRight⟩ :=
        mem_closure_iff.1 hxRightClosure (interior (closure p.left)) isOpen_interior hxInterior
      exact False.elim
        (Set.disjoint_left.1 (p.disjoint.closure_left p.isOpen_right)
          (interior_subset hyInterior) hyRight)
  · exact (subset_interior_iff_isOpen.2 p.isOpen_left).trans
      (interior_mono subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_left_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_left_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_left_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_left_eq

theorem interior_closure_right_eq (p : ComplementPair S)
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    interior (closure p.right) = p.right := by
  apply Set.Subset.antisymm
  · intro x hxInterior
    have hxClosure : x ∈ closure p.right := interior_subset hxInterior
    rw [p.closure_right_eq hSright] at hxClosure
    rcases hxClosure with hxRight | hxS
    · exact hxRight
    · have hxLeftClosure : x ∈ closure p.left := hSleft hxS
      obtain ⟨y, hyInterior, hyLeft⟩ :=
        mem_closure_iff.1 hxLeftClosure (interior (closure p.right)) isOpen_interior hxInterior
      exact False.elim
        (Set.disjoint_left.1 (p.disjoint.closure_right p.isOpen_left)
          hyLeft (interior_subset hyInterior))
  · exact (subset_interior_iff_isOpen.2 p.isOpen_right).trans
      (interior_mono subset_closure)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_right_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_right_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_right_eq ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.interior_closure_right_eq

def toSphereSides (p : ComplementPair S)
    (hCompact : IsCompact (closure p.left))
    (hNoncompact : ¬ IsCompact (closure p.right))
    (hSleft : S ⊆ closure p.left) (hSright : S ⊆ closure p.right) :
    SphereSides S where
  compactSide := p.left
  endSide := p.right
  isOpen_compactSide := p.isOpen_left
  isOpen_endSide := p.isOpen_right
  isConnected_compactSide := p.isConnected_left
  isConnected_endSide := p.isConnected_right
  disjoint := p.disjoint
  union_eq_compl := p.union_eq_compl
  isCompact_closure_compactSide := hCompact
  not_isCompact_closure_endSide := hNoncompact
  frontier_compactSide := p.frontier_left_eq hSleft
  frontier_endSide := p.frontier_right_eq hSright
  closure_compactSide := p.closure_left_eq hSleft
  closure_endSide := p.closure_right_eq hSright
  interior_closure_compactSide := p.interior_closure_left_eq hSleft hSright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.toSphereSides then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.toSphereSides"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.toSphereSides ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.toSphereSides


def swap (p : ComplementPair S) : ComplementPair S where
  left := p.right
  right := p.left
  isOpen_left := p.isOpen_right
  isOpen_right := p.isOpen_left
  isConnected_left := p.isConnected_right
  isConnected_right := p.isConnected_left
  disjoint := p.disjoint.symm
  union_eq_compl := by rw [_root_.Set.union_comm, p.union_eq_compl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.swap ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.swap

theorem sphere_subset_right_of_sphere_subset_left
    {T : Set X}
    (p : ComplementPair S) (q : ComplementPair T)
    (hS : S ⊆ closure p.right)
    (hsub : T ⊆ p.left) (hmeet : (p.right ∩ q.right).Nonempty) : S ⊆ q.right := by
  have havoid : p.right ⊆ Tᶜ := by
    intro x hx hxT
    exact p.disjoint.le_bot ⟨hsub hxT, hx⟩
  have hright : p.right ⊆ q.right := by
    rcases q.subset_left_or_subset_right p.isConnected_right.isPreconnected havoid with h | h
    · obtain ⟨x, hx, hxq⟩ := hmeet
      exact False.elim (q.disjoint.le_bot ⟨h hx, hxq⟩)
    · exact h
  intro x hx
  have hcl : x ∈ closure q.right := closure_mono hright (hS hx)
  have hxT : x ∈ Tᶜ := fun hxT => p.left_disjoint_sphere.le_bot ⟨hsub hxT, hx⟩
  rw [← q.union_eq_compl] at hxT
  rcases hxT with hleft | hright
  · exact False.elim ((q.disjoint.closure_right q.isOpen_left).le_bot ⟨hleft, hcl⟩)
  · exact hright

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.sphere_subset_right_of_sphere_subset_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.sphere_subset_right_of_sphere_subset_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.sphere_subset_right_of_sphere_subset_left ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.sphere_subset_right_of_sphere_subset_left

theorem inter_sphere_nonempty_of_isPreconnected
    (p : ComplementPair S) (hC : IsPreconnected C)
    (hl : (C ∩ p.left).Nonempty) (hr : (C ∩ p.right).Nonempty) :
    (C ∩ S).Nonempty := by
  by_contra hnone
  have havoid : C ⊆ Sᶜ := by
    intro x hx hxS
    exact hnone ⟨x, hx, hxS⟩
  rcases p.subset_left_or_subset_right hC havoid with h | h
  · obtain ⟨x, hx, hxr⟩ := hr
    exact p.disjoint.le_bot ⟨h hx, hxr⟩
  · obtain ⟨x, hx, hxl⟩ := hl
    exact p.disjoint.le_bot ⟨hxl, h hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.inter_sphere_nonempty_of_isPreconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.ComplementPair.inter_sphere_nonempty_of_isPreconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.ComplementPair.inter_sphere_nonempty_of_isPreconnected ``Submission.DifferentialGeometry.Topology.SphereSeparation.ComplementPair.inter_sphere_nonempty_of_isPreconnected


end ComplementPair

end DifferentialGeometry.Topology.SphereSeparation
