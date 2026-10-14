import Submission.DifferentialGeometry.Topology.SimplicialComplex.Incidence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

noncomputable section

variable {ι : Type*} (K : PreAbstractSimplicialComplex ι) [Finite K.faces]


def faceEulerChar : ℤ := ∑ s ∈ (Set.toFinite K.faces).toFinset, -(-1 : ℤ) ^ s.card

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar


theorem faceEulerChar_eq_sum (d : ℕ) (hd : ∀ s ∈ K, s.card ≤ d) :
    faceEulerChar K = ∑ n ∈ _root_.Finset.range (d + 1), -(-1 : ℤ) ^ n * (facesOfCard K n).card := by
  classical
  have hmap : ∀ s ∈ (Set.toFinite K.faces).toFinset, s.card ∈ _root_.Finset.range (d + 1) := by
    intro s hs
    exact mem_range.mpr (Nat.lt_succ_of_le (hd s ((Set.toFinite K.faces).mem_toFinset.mp hs)))
  unfold faceEulerChar
  rw [← _root_.Finset.sum_fiberwise_of_maps_to hmap]
  apply _root_.Finset.sum_congr rfl
  intro n hn
  change (∑ s ∈ facesOfCard K n, -(-1 : ℤ) ^ s.card) = _
  calc
    _ = ∑ _s ∈ facesOfCard K n, -(-1 : ℤ) ^ n := by
      apply _root_.Finset.sum_congr rfl
      intro s hs
      rw [((mem_facesOfCard K).mp hs).2]
    _ = _ := by simp [mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_sum ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_sum


theorem faceEulerChar_eq_of_card_le_four (hd : ∀ s ∈ K, s.card ≤ 4) :
    faceEulerChar K = (facesOfCard K 1).card - (facesOfCard K 2).card +
      (facesOfCard K 3).card - (facesOfCard K 4).card := by
  rw [faceEulerChar_eq_sum K 4 hd]
  simp [_root_.Finset.sum_range_succ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_four then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_four"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_four ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_four


theorem faceEulerChar_eq_of_card_le_three (hd : ∀ s ∈ K, s.card ≤ 3) :
    faceEulerChar K = (facesOfCard K 1).card - (facesOfCard K 2).card +
      (facesOfCard K 3).card := by
  rw [faceEulerChar_eq_sum K 3 hd]
  simp [_root_.Finset.sum_range_succ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_three ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_three


theorem faceEulerChar_eq_of_card_le_two (hd : ∀ s ∈ K, s.card ≤ 2) :
    faceEulerChar K = (facesOfCard K 1).card - (facesOfCard K 2).card := by
  rw [faceEulerChar_eq_sum K 2 hd]
  simp [_root_.Finset.sum_range_succ, sub_eq_add_neg, add_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_two ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_eq_of_card_le_two


@[simp]
theorem faceEulerChar_bot : faceEulerChar (⊥ : PreAbstractSimplicialComplex ι) = 0 := by
  have h : (Set.toFinite (⊥ : PreAbstractSimplicialComplex ι).faces).toFinset = ∅ := by
    ext s
    simp only [Set.Finite.mem_toFinset, _root_.Finset.notMem_empty, iff_false]
    exact id
  simp [faceEulerChar, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_bot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_bot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_bot ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_bot


theorem faceEulerChar_sup_add_faceEulerChar_inf
    (L : PreAbstractSimplicialComplex ι) [Finite L.faces] :
    faceEulerChar (K ⊔ L) + faceEulerChar (K ⊓ L) =
      faceEulerChar K + faceEulerChar L := by
  classical
  have hsup : (Set.toFinite (K ⊔ L).faces).toFinset =
      (Set.toFinite K.faces).toFinset ∪ (Set.toFinite L.faces).toFinset := by
    ext s
    simp only [Set.Finite.mem_toFinset, _root_.Finset.mem_union]
    rfl
  have hinf : (Set.toFinite (K ⊓ L).faces).toFinset =
      (Set.toFinite K.faces).toFinset ∩ (Set.toFinite L.faces).toFinset := by
    ext s
    simp only [Set.Finite.mem_toFinset, _root_.Finset.mem_inter]
    rfl
  simp only [faceEulerChar, hsup, hinf]
  exact _root_.Finset.sum_union_inter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_sup_add_faceEulerChar_inf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_sup_add_faceEulerChar_inf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_sup_add_faceEulerChar_inf ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_sup_add_faceEulerChar_inf


theorem faceEulerChar_map_of_injective {κ : Type*} [DecidableEq κ]
    (f : ι → κ) (hf : Function.Injective f) :
    faceEulerChar (K.map f) = faceEulerChar K := by
  classical
  have hmap : (Set.toFinite (K.map f).faces).toFinset =
      (Set.toFinite K.faces).toFinset.image (fun s => s.image f) := by
    ext s
    simp only [Set.Finite.mem_toFinset, _root_.Finset.mem_image]
    rfl
  rw [faceEulerChar, hmap, _root_.Finset.sum_image]
  · apply _root_.Finset.sum_congr rfl
    intro s hs
    rw [_root_.Finset.card_image_of_injective _ hf]
  · exact (_root_.Finset.image_injective hf).injOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_map_of_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_map_of_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_map_of_injective ``Submission.DifferentialGeometry.Topology.SimplicialComplex.faceEulerChar_map_of_injective

end

end DifferentialGeometry.Topology.SimplicialComplex
