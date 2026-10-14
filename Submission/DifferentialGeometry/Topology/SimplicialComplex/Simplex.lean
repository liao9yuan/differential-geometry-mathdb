import Submission.DifferentialGeometry.Topology.SimplicialComplex.BoundaryCounting
import Mathlib.Data.Nat.Choose.Sum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

variable {ι : Type*}


def simplex (vertices : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ s ⊆ vertices}
  isRelLowerSet_faces := fun {_s} hs => ⟨hs.1, fun _ hts ht => ⟨ht, hts.trans hs.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.simplex


def boundarySimplex (vertices : Finset ι) : PreAbstractSimplicialComplex ι where
  faces := {s | s.Nonempty ∧ s ⊂ vertices}
  isRelLowerSet_faces := fun {_s} hs => ⟨hs.1, fun _ hts ht => ⟨ht, lt_of_le_of_lt hts hs.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex

@[simp]
theorem mem_simplex {vertices s : Finset ι} :
    s ∈ simplex vertices ↔ s.Nonempty ∧ s ⊆ vertices := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_simplex

@[simp]
theorem mem_boundarySimplex {vertices s : Finset ι} :
    s ∈ boundarySimplex vertices ↔ s.Nonempty ∧ s ⊂ vertices := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.mem_boundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.mem_boundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.mem_boundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.mem_boundarySimplex

theorem boundarySimplex_le_simplex (vertices : Finset ι) :
    boundarySimplex vertices ≤ simplex vertices :=
  fun _ hs => ⟨hs.1, hs.2.le⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_le_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_le_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_le_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_le_simplex

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesSimplex (vertices : Finset ι) : Finite (simplex vertices).faces := by
  classical
  apply Set.Finite.to_subtype
  exact vertices.powerset.finite_toSet.subset fun s hs => mem_powerset.mpr hs.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesSimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesSimplex

instance _root_.Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBoundarySimplex (vertices : Finset ι) : Finite (boundarySimplex vertices).faces :=
  Set.Finite.to_subtype ((Set.toFinite (simplex vertices).faces).subset
    (boundarySimplex_le_simplex vertices))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBoundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBoundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBoundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.instFiniteElemFinsetFacesBoundarySimplex

@[simp]
theorem simplex_empty : simplex (∅ : Finset ι) = ⊥ := by
  ext s
  change (s.Nonempty ∧ s ⊆ (∅ : Finset ι)) ↔ False
  simp only [_root_.Finset.subset_empty]
  constructor
  · rintro ⟨h, rfl⟩
    exact h.ne_empty rfl
  · exact False.elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.simplex_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.simplex_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.simplex_empty ``Submission.DifferentialGeometry.Topology.SimplicialComplex.simplex_empty

@[simp]
theorem boundarySimplex_empty : boundarySimplex (∅ : Finset ι) = ⊥ := by
  apply le_antisymm
  · simpa only [simplex_empty] using boundarySimplex_le_simplex (∅ : Finset ι)
  · exact bot_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_empty ``Submission.DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_empty


theorem link_simplex [DecidableEq ι] {vertices s : Finset ι} (hs : s ⊆ vertices) :
    link (simplex vertices) s = simplex (vertices \ s) := by
  ext t
  change (t.Nonempty ∧ Disjoint s t ∧ (s ∪ t).Nonempty ∧ s ∪ t ⊆ vertices) ↔
    (t.Nonempty ∧ t ⊆ vertices \ s)
  simp only [_root_.Finset.subset_sdiff, _root_.Finset.union_subset_iff]
  constructor
  · rintro ⟨ht, hdisj, _, _, htv⟩
    exact ⟨ht, htv, hdisj.symm⟩
  · rintro ⟨ht, htv, hdisj⟩
    exact ⟨ht, hdisj.symm, ht.mono _root_.Finset.subset_union_right, hs, htv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.link_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.link_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.link_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.link_simplex


theorem link_boundarySimplex [DecidableEq ι] {vertices s : Finset ι} (hs : s ⊆ vertices) :
    link (boundarySimplex vertices) s = boundarySimplex (vertices \ s) := by
  ext t
  change (t.Nonempty ∧ Disjoint s t ∧ (s ∪ t).Nonempty ∧ s ∪ t ⊂ vertices) ↔
    (t.Nonempty ∧ t ⊂ vertices \ s)
  constructor
  · rintro ⟨ht, hdisj, _, hproper⟩
    refine ⟨ht, lt_of_le_of_ne ?_ ?_⟩
    · exact subset_sdiff.mpr ⟨subset_union_right.trans hproper.le, hdisj.symm⟩
    · intro heq
      exact hproper.ne (by rw [heq, _root_.Finset.union_sdiff_of_subset hs])
  · rintro ⟨ht, hproper⟩
    obtain ⟨htv, hdisj⟩ := subset_sdiff.mp hproper.le
    refine ⟨ht, hdisj.symm, ht.mono _root_.Finset.subset_union_right,
      lt_of_le_of_ne (_root_.Finset.union_subset hs htv) ?_⟩
    intro heq
    have heq' := congrArg (fun u : Finset ι => u \ s) heq
    rw [_root_.Finset.union_sdiff_cancel_left hdisj.symm] at heq'
    exact hproper.ne heq'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.link_boundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.link_boundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.link_boundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.link_boundarySimplex

noncomputable section


theorem facesOfCard_simplex (vertices : Finset ι) (n : ℕ) (hn : 0 < n) :
    facesOfCard (simplex vertices) n = vertices.powersetCard n := by
  classical
  ext s
  simp only [mem_facesOfCard, mem_simplex, _root_.Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hsv⟩, hc⟩
    exact ⟨hsv, hc⟩
  · rintro ⟨hsv, hc⟩
    exact ⟨⟨card_pos.mp (hc ▸ hn), hsv⟩, hc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_simplex

theorem card_facesOfCard_simplex (vertices : Finset ι) (n : ℕ) (hn : 0 < n) :
    (facesOfCard (simplex vertices) n).card = vertices.card.choose n := by
  rw [facesOfCard_simplex vertices n hn, _root_.Finset.card_powersetCard]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_simplex


theorem facesOfCard_boundarySimplex [DecidableEq ι] (vertices : Finset ι) (n : ℕ) :
    facesOfCard (boundarySimplex vertices) n =
      (facesOfCard (simplex vertices) n).erase vertices := by
  ext s
  simp only [mem_facesOfCard, mem_boundarySimplex, _root_.Finset.mem_erase, mem_simplex,
    lt_iff_le_and_ne]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex


theorem facesOfCard_boundarySimplex_of_lt (vertices : Finset ι) (n : ℕ)
    (hn : 0 < n) (hlt : n < vertices.card) :
    facesOfCard (boundarySimplex vertices) n = vertices.powersetCard n := by
  classical
  rw [facesOfCard_boundarySimplex, facesOfCard_simplex vertices n hn,
    _root_.Finset.erase_eq_of_notMem]
  simp only [_root_.Finset.mem_powersetCard, subset_refl, true_and]
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_of_lt ``Submission.DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_of_lt

theorem card_facesOfCard_boundarySimplex_of_lt (vertices : Finset ι) (n : ℕ)
    (hn : 0 < n) (hlt : n < vertices.card) :
    (facesOfCard (boundarySimplex vertices) n).card = vertices.card.choose n := by
  rw [facesOfCard_boundarySimplex_of_lt vertices n hn hlt, _root_.Finset.card_powersetCard]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_boundarySimplex_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_boundarySimplex_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_boundarySimplex_of_lt ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_facesOfCard_boundarySimplex_of_lt


theorem facesOfCard_boundarySimplex_eq_empty (vertices : Finset ι) (n : ℕ)
    (hn : vertices.card ≤ n) : facesOfCard (boundarySimplex vertices) n = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro s hs
  obtain ⟨⟨_, hproper⟩, hc⟩ := (mem_facesOfCard (boundarySimplex vertices)).mp hs
  have hlt := _root_.Finset.card_lt_card hproper
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_eq_empty ``Submission.DifferentialGeometry.Topology.SimplicialComplex.facesOfCard_boundarySimplex_eq_empty

private theorem simplex_faces_toFinset [DecidableEq ι] (vertices : Finset ι) :
    (Set.toFinite (simplex vertices).faces).toFinset = vertices.powerset.erase ∅ := by
  ext s
  simp only [Set.Finite.mem_toFinset, _root_.Finset.mem_erase, _root_.Finset.mem_powerset]
  change (s.Nonempty ∧ s ⊆ vertices) ↔ (s ≠ ∅ ∧ s ⊆ vertices)
  rw [_root_.Finset.nonempty_iff_ne_empty]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplicialComplex.simplex_faces_toFinset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplicialComplex.simplex_faces_toFinset target :: scope.openDecls } }

private theorem boundarySimplex_faces_toFinset [DecidableEq ι] (vertices : Finset ι) :
    (Set.toFinite (boundarySimplex vertices).faces).toFinset =
      (Set.toFinite (simplex vertices).faces).toFinset.erase vertices := by
  ext s
  simp only [Set.Finite.mem_toFinset, _root_.Finset.mem_erase]
  change (s.Nonempty ∧ s ⊂ vertices) ↔ (s ≠ vertices ∧ s.Nonempty ∧ s ⊆ vertices)
  rw [lt_iff_le_and_ne]
  tauto

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_faces_toFinset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplicialComplex.boundarySimplex_faces_toFinset target :: scope.openDecls } }


theorem faceEulerChar_simplex {vertices : Finset ι} (hvertices : vertices.Nonempty) :
    faceEulerChar (simplex vertices) = 1 := by
  classical
  rw [faceEulerChar, simplex_faces_toFinset, _root_.Finset.sum_neg_distrib]
  have hsum := _root_.Finset.sum_erase_add (s := vertices.powerset)
    (f := fun s : Finset ι => (-1 : ℤ) ^ s.card) (mem_powerset.mpr (_root_.Finset.empty_subset vertices))
  rw [_root_.Finset.sum_powerset_neg_one_pow_card_of_nonempty hvertices] at hsum
  simp only [_root_.Finset.card_empty, pow_zero] at hsum
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_simplex


theorem faceEulerChar_boundarySimplex {vertices : Finset ι} (hvertices : vertices.Nonempty) :
    faceEulerChar (boundarySimplex vertices) = 1 + (-1 : ℤ) ^ vertices.card := by
  classical
  have hmem : vertices ∈ (Set.toFinite (simplex vertices).faces).toFinset := by
    exact (Set.toFinite (simplex vertices).faces).mem_toFinset.mpr ⟨hvertices, subset_refl _⟩
  have hsum := _root_.Finset.sum_erase_add (s := (Set.toFinite (simplex vertices).faces).toFinset)
    (f := fun s : Finset ι => -(-1 : ℤ) ^ s.card) hmem
  have hsimplex := faceEulerChar_simplex hvertices
  rw [faceEulerChar, boundarySimplex_faces_toFinset]
  change (∑ s ∈ (Set.toFinite (simplex vertices).faces).toFinset.erase vertices,
    -(-1 : ℤ) ^ s.card) + -(-1 : ℤ) ^ vertices.card =
    faceEulerChar (simplex vertices) at hsum
  rw [hsimplex] at hsum
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex


theorem faceEulerChar_link_simplex [DecidableEq ι] {vertices s : Finset ι}
    (hs : s ⊂ vertices) : faceEulerChar (link (simplex vertices) s) = 1 := by
  simpa only [link_simplex hs.le] using
    faceEulerChar_simplex (sdiff_nonempty.mpr hs.not_ge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_simplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_simplex


theorem faceEulerChar_link_boundarySimplex [DecidableEq ι] {vertices s : Finset ι}
    (hs : s ⊂ vertices) :
    faceEulerChar (link (boundarySimplex vertices) s) =
      1 + (-1 : ℤ) ^ (vertices.card - s.card) := by
  simpa only [link_boundarySimplex hs.le, _root_.Finset.card_sdiff_of_subset hs.le] using
    faceEulerChar_boundarySimplex (sdiff_nonempty.mpr hs.not_ge)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_boundarySimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_boundarySimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_boundarySimplex ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_link_boundarySimplex


theorem tetrahedron_face_counts :
    (facesOfCard (simplex (_root_.Finset.univ : Finset (Fin 4))) 1).card = 4 ∧
    (facesOfCard (simplex (_root_.Finset.univ : Finset (Fin 4))) 2).card = 6 ∧
    (facesOfCard (simplex (_root_.Finset.univ : Finset (Fin 4))) 3).card = 4 ∧
    (facesOfCard (simplex (_root_.Finset.univ : Finset (Fin 4))) 4).card = 1 := by
  norm_num [card_facesOfCard_simplex, Nat.choose]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_face_counts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_face_counts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_face_counts ``Submission.DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_face_counts


theorem tetrahedron_boundary_face_counts :
    (facesOfCard (boundarySimplex (_root_.Finset.univ : Finset (Fin 4))) 1).card = 4 ∧
    (facesOfCard (boundarySimplex (_root_.Finset.univ : Finset (Fin 4))) 2).card = 6 ∧
    (facesOfCard (boundarySimplex (_root_.Finset.univ : Finset (Fin 4))) 3).card = 4 ∧
    (facesOfCard (boundarySimplex (_root_.Finset.univ : Finset (Fin 4))) 4).card = 0 := by
  rw [card_facesOfCard_boundarySimplex_of_lt _ 1 (by omega) (by simp),
    card_facesOfCard_boundarySimplex_of_lt _ 2 (by omega) (by simp),
    card_facesOfCard_boundarySimplex_of_lt _ 3 (by omega) (by simp),
    facesOfCard_boundarySimplex_eq_empty _ 4 (by simp)]
  norm_num [Nat.choose]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_face_counts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_face_counts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_face_counts ``Submission.DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_face_counts

theorem faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four
    (vertices : Finset ι) (hcard : vertices.card = 4) :
    faceEulerChar (boundarySimplex vertices) = 2 * faceEulerChar (simplex vertices) := by
  classical
  have hproper {s : Finset ι} {k : ℕ}
      (hs : s ∈ facesOfCard (simplex vertices) k) (hk : k < 4) : s ⊂ vertices := by
    obtain ⟨⟨_, hsub⟩, hsc⟩ := (mem_facesOfCard (simplex vertices)).mp hs
    apply lt_of_le_of_ne hsub
    intro heq
    have := congrArg Finset.card heq
    omega
  apply faceEulerChar_eq_two_mul_of_link_counts (simplex vertices) (boundarySimplex vertices)
    (boundarySimplex_le_simplex vertices)
  · intro u hu
    exact hcard ▸ _root_.Finset.card_le_card hu.2
  · intro u hu
    have := _root_.Finset.card_lt_card hu.2
    omega
  · intro s hs
    have hsp := hproper hs (by decide)
    obtain ⟨⟨hsne, hsub⟩, hsc⟩ := (mem_facesOfCard (simplex vertices)).mp hs
    have hboundary : s ∈ boundarySimplex vertices := ⟨hsne, hsp⟩
    rw [if_pos hboundary]
    have hlink : (facesOfCard (link (simplex vertices) s) 1).card = 1 := by
      simpa [link_simplex hsub, _root_.Finset.card_sdiff_of_subset hsub, hcard, hsc] using
        card_facesOfCard_simplex (vertices \ s) 1 (by decide)
    have hco := (card_facesOfCard_link (simplex vertices) s 1 (by decide)).symm.trans hlink
    simpa only [hsc] using hco
  · intro s hs
    have hsp := hproper hs (by decide)
    have hboundary : s ∈ boundarySimplex vertices :=
      ⟨((mem_facesOfCard (simplex vertices)).mp hs).1.1, hsp⟩
    rw [if_pos hboundary]
    exact faceEulerChar_link_simplex hsp
  · intro s hs
    have hsp := hproper hs (by decide)
    have hboundary : s ∈ boundarySimplex vertices :=
      ⟨((mem_facesOfCard (simplex vertices)).mp hs).1.1, hsp⟩
    rw [if_pos hboundary]
    exact faceEulerChar_link_simplex hsp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four


theorem tetrahedron_boundary_faceEulerChar :
    faceEulerChar (boundarySimplex (_root_.Finset.univ : Finset (Fin 4))) =
      2 * faceEulerChar (simplex (_root_.Finset.univ : Finset (Fin 4))) :=
  faceEulerChar_boundarySimplex_eq_two_mul_of_card_eq_four _root_.Finset.univ (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_faceEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_faceEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_faceEulerChar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.tetrahedron_boundary_faceEulerChar

end

end DifferentialGeometry.Topology.SimplicialComplex
