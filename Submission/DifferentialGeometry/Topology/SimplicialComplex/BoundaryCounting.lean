import Submission.DifferentialGeometry.Topology.SimplicialComplex.LinkCounting
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

noncomputable section

variable {ι : Type*}
  (K L : PreAbstractSimplicialComplex ι) [Finite K.faces] [Finite L.faces]

open _root_.Classical in
private theorem sum_ite_mem_faces (hLK : L ≤ K) (k : ℕ) (a b : ℤ) :
    ∑ s ∈ facesOfCard K k, (if s ∈ L then a else b) =
      b * (facesOfCard K k).card + (a - b) * (facesOfCard L k).card := by
  classical
  have hf : (facesOfCard K k).filter (· ∈ L) = facesOfCard L k := by
    ext s
    simp only [_root_.Finset.mem_filter, mem_facesOfCard]
    constructor
    · rintro ⟨⟨_, hc⟩, hs⟩
      exact ⟨hs, hc⟩
    · rintro ⟨hs, hc⟩
      exact ⟨⟨hLK hs, hc⟩, hs⟩
  calc
    _ = ∑ s ∈ facesOfCard K k, (b + if s ∈ L then a - b else 0) := by
      apply _root_.Finset.sum_congr rfl
      intro s hs
      split_ifs <;> ring
    _ = _ := by
      rw [_root_.Finset.sum_add_distrib, ← _root_.Finset.sum_filter, hf]
      simp [mul_comm, sub_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplicialComplex.sum_ite_mem_faces
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplicialComplex.sum_ite_mem_faces target :: scope.openDecls } }

variable [DecidableEq ι]

open _root_.Classical in
theorem card_boundary_triangles (hLK : L ≤ K)
    (htri : ∀ s ∈ facesOfCard K 3, (cofaces K s 4).card = if s ∈ L then 1 else 2) :
    ((facesOfCard L 3).card : ℤ) =
      2 * (facesOfCard K 3).card - 4 * (facesOfCard K 4).card := by
  classical
  have hcount : (∑ s ∈ facesOfCard K 3, ((cofaces K s 4).card : ℤ)) =
      4 * (facesOfCard K 4).card := by
    exact_mod_cast sum_card_cofaces K 3 4 (by decide)
  have hlocal : (∑ s ∈ facesOfCard K 3, ((cofaces K s 4).card : ℤ)) =
      2 * (facesOfCard K 3).card - (facesOfCard L 3).card := by
    calc
      _ = ∑ s ∈ facesOfCard K 3, (if s ∈ L then (1 : ℤ) else 2) := by
        apply _root_.Finset.sum_congr rfl
        intro s hs
        rw [htri s hs]
        split_ifs <;> norm_num
      _ = _ := by rw [sum_ite_mem_faces K L hLK]; ring
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_boundary_triangles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_boundary_triangles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_boundary_triangles ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_boundary_triangles

open _root_.Classical in
theorem card_boundary_edges (hLK : L ≤ K) (hd : ∀ u ∈ K, u.card ≤ 4)
    (hedge : ∀ s ∈ facesOfCard K 2,
      faceEulerChar (link K s) = if s ∈ L then 1 else 0) :
    ((facesOfCard L 2).card : ℤ) =
      3 * (facesOfCard K 3).card - 6 * (facesOfCard K 4).card := by
  classical
  rw [← sum_faceEulerChar_link_edges K hd]
  calc
    _ = ∑ s ∈ facesOfCard K 2, (if s ∈ L then (1 : ℤ) else 0) := by
      rw [sum_ite_mem_faces K L hLK]
      ring
    _ = _ := _root_.Finset.sum_congr rfl fun s hs => (hedge s hs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_boundary_edges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_boundary_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_boundary_edges ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_boundary_edges

open _root_.Classical in
theorem card_boundary_vertices (hLK : L ≤ K) (hd : ∀ u ∈ K, u.card ≤ 4)
    (hvertex : ∀ s ∈ facesOfCard K 1,
      faceEulerChar (link K s) = if s ∈ L then 1 else 2) :
    ((facesOfCard L 1).card : ℤ) = 2 * (facesOfCard K 1).card -
      2 * (facesOfCard K 2).card + 3 * (facesOfCard K 3).card -
        4 * (facesOfCard K 4).card := by
  classical
  have hlocal : (∑ s ∈ facesOfCard K 1, faceEulerChar (link K s)) =
      2 * (facesOfCard K 1).card - (facesOfCard L 1).card := by
    calc
      _ = ∑ s ∈ facesOfCard K 1, (if s ∈ L then (1 : ℤ) else 2) :=
        _root_.Finset.sum_congr rfl fun s hs => hvertex s hs
      _ = _ := by rw [sum_ite_mem_faces K L hLK]; ring
  have hcount := sum_faceEulerChar_link_vertices K hd
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_boundary_vertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_boundary_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_boundary_vertices ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_boundary_vertices

open _root_.Classical in
theorem faceEulerChar_eq_two_mul_of_link_counts (hLK : L ≤ K)
    (hK : ∀ u ∈ K, u.card ≤ 4) (hL : ∀ u ∈ L, u.card ≤ 3)
    (htri : ∀ s ∈ facesOfCard K 3, (cofaces K s 4).card = if s ∈ L then 1 else 2)
    (hedge : ∀ s ∈ facesOfCard K 2,
      faceEulerChar (link K s) = if s ∈ L then 1 else 0)
    (hvertex : ∀ s ∈ facesOfCard K 1,
      faceEulerChar (link K s) = if s ∈ L then 1 else 2) :
    faceEulerChar L = 2 * faceEulerChar K := by
  rw [faceEulerChar_eq_of_card_le_three L hL, faceEulerChar_eq_of_card_le_four K hK,
    card_boundary_triangles K L hLK htri, card_boundary_edges K L hLK hK hedge,
    card_boundary_vertices K L hLK hK hvertex]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_two_mul_of_link_counts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_two_mul_of_link_counts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_two_mul_of_link_counts ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_two_mul_of_link_counts

end

end DifferentialGeometry.Topology.SimplicialComplex
