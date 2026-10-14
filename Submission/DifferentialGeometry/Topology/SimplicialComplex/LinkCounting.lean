import Submission.DifferentialGeometry.Topology.SimplicialComplex.EulerCharacteristic
import Mathlib.Tactic.NormNum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

noncomputable section

variable {ι : Type*} [DecidableEq ι]
  (K : PreAbstractSimplicialComplex ι)


theorem card_add_card_le_of_mem_link {d : ℕ} (hd : ∀ u ∈ K, u.card ≤ d)
    {s t : Finset ι} (ht : t ∈ link K s) : s.card + t.card ≤ d := by
  rw [← _root_.Finset.card_union_of_disjoint ht.2.1]
  exact hd _ ht.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.card_add_card_le_of_mem_link then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.card_add_card_le_of_mem_link"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.card_add_card_le_of_mem_link ``Submission.DifferentialGeometry.Topology.SimplicialComplex.card_add_card_le_of_mem_link

variable [Finite K.faces]


theorem sum_faceEulerChar_link_edges (hd : ∀ u ∈ K, u.card ≤ 4) :
    ∑ s ∈ facesOfCard K 2, faceEulerChar (link K s) =
      3 * (facesOfCard K 3).card - 6 * (facesOfCard K 4).card := by
  have hsum (n : ℕ) (hn : 0 < n) :
      (∑ s ∈ facesOfCard K 2, ((facesOfCard (link K s) n).card : ℤ)) =
        ((2 + n).choose 2 : ℤ) * (facesOfCard K (2 + n)).card := by
    exact_mod_cast sum_card_facesOfCard_link K 2 n (by decide) hn
  calc
    _ = ∑ s ∈ facesOfCard K 2,
        (((facesOfCard (link K s) 1).card : ℤ) -
          (facesOfCard (link K s) 2).card) := by
      apply _root_.Finset.sum_congr rfl
      intro s hs
      apply faceEulerChar_eq_of_card_le_two
      intro t ht
      have hc := card_add_card_le_of_mem_link K hd ht
      have hs' := ((mem_facesOfCard K).mp hs).2
      omega
    _ = _ := by
      rw [_root_.Finset.sum_sub_distrib, hsum 1 (by decide), hsum 2 (by decide)]
      norm_num [Nat.choose]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_edges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_edges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_edges ``Submission.DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_edges


theorem sum_faceEulerChar_link_vertices (hd : ∀ u ∈ K, u.card ≤ 4) :
    ∑ s ∈ facesOfCard K 1, faceEulerChar (link K s) =
      2 * (facesOfCard K 2).card - 3 * (facesOfCard K 3).card +
        4 * (facesOfCard K 4).card := by
  have hsum (n : ℕ) (hn : 0 < n) :
      (∑ s ∈ facesOfCard K 1, ((facesOfCard (link K s) n).card : ℤ)) =
        ((1 + n).choose 1 : ℤ) * (facesOfCard K (1 + n)).card := by
    exact_mod_cast sum_card_facesOfCard_link K 1 n (by decide) hn
  calc
    _ = ∑ s ∈ facesOfCard K 1,
        (((facesOfCard (link K s) 1).card : ℤ) -
          (facesOfCard (link K s) 2).card + (facesOfCard (link K s) 3).card) := by
      apply _root_.Finset.sum_congr rfl
      intro s hs
      apply faceEulerChar_eq_of_card_le_three
      intro t ht
      have hc := card_add_card_le_of_mem_link K hd ht
      have hs' := ((mem_facesOfCard K).mp hs).2
      omega
    _ = _ := by
      rw [_root_.Finset.sum_add_distrib, _root_.Finset.sum_sub_distrib,
        hsum 1 (by decide), hsum 2 (by decide), hsum 3 (by decide)]
      norm_num [Nat.choose]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_vertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_vertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_vertices ``Submission.DifferentialGeometry.Topology.SimplicialComplex.sum_faceEulerChar_link_vertices

end

end DifferentialGeometry.Topology.SimplicialComplex
