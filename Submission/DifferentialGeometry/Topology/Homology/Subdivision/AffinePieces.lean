import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Barycentric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology


def BarycentricFlag (n : ℕ) : Type :=
  match n with
  | 0 => Unit
  | n + 1 => Fin (n + 2) × BarycentricFlag n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.BarycentricFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.BarycentricFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.BarycentricFlag ``Submission.DifferentialGeometry.Homology.BarycentricFlag

instance _root_.Submission.DifferentialGeometry.Homology.instFintypeBarycentricFlag (n : ℕ) : Fintype (BarycentricFlag n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n hn => exact inferInstanceAs (Fintype (Fin (n + 2) × BarycentricFlag n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.instFintypeBarycentricFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.instFintypeBarycentricFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.instFintypeBarycentricFlag ``Submission.DifferentialGeometry.Homology.instFintypeBarycentricFlag


theorem card_barycentricFlag (n : ℕ) : Fintype.card (BarycentricFlag n) = (n + 1).factorial := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change Fintype.card (Fin (n + 2) × BarycentricFlag n) = (n + 1 + 1).factorial
    rw [Fintype.card_prod, Fintype.card_fin, hn, Nat.factorial_succ (n + 1)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.card_barycentricFlag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.card_barycentricFlag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.card_barycentricFlag ``Submission.DifferentialGeometry.Homology.card_barycentricFlag


def barycentricFlagSign (n : ℕ) : BarycentricFlag n → ℤ :=
  match n with
  | 0 => fun _ ↦ 1
  | n + 1 => fun p ↦ (-1) ^ p.1.val * barycentricFlagSign n p.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricFlagSign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricFlagSign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricFlagSign ``Submission.DifferentialGeometry.Homology.barycentricFlagSign

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def barycentricPieceVertices (n : ℕ) :
    (Fin (n + 1) → E) → BarycentricFlag n → Fin (n + 1) → E :=
  match n with
  | 0 => fun v _ ↦ v
  | n + 1 => fun v p ↦ Fin.cons (Finset.univ.centerMass (fun _ ↦ (1 : ℝ)) v)
      (barycentricPieceVertices n (v ∘ p.1.succAbove) p.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricPieceVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricPieceVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricPieceVertices ``Submission.DifferentialGeometry.Homology.barycentricPieceVertices


theorem barycentricPieceVertices_mem (n : ℕ) (v : Fin (n + 1) → E)
    (p : BarycentricFlag n) {s : Set E} (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s)
    (i : Fin (n + 1)) : barycentricPieceVertices n v p i ∈ s := by
  induction n with
  | zero => exact hv i
  | succ n hn =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact hs.centerMass_mem (fun _ _ ↦ zero_le_one)
        (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos (n + 1)) :
          (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ))) (fun j _ ↦ hv j)
    · exact hn (v ∘ p.1.succAbove) p.2 (fun j ↦ hv (p.1.succAbove j)) j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricPieceVertices_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricPieceVertices_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricPieceVertices_mem ``Submission.DifferentialGeometry.Homology.barycentricPieceVertices_mem

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


theorem affineSubdivisionMap_pieces (n : ℕ) (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) ≫
        affineSubdivisionMap R n =
      ∑ p : BarycentricFlag n, barycentricFlagSign n p •
        (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex
          (affineSingularSimplex (barycentricPieceVertices n v p)) := by
  induction n with
  | zero =>
    rw [affineSubdivisionMap_zero, Category.comp_id]
    change _ = ∑ _ : Unit, (1 : ℤ) • _
    simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
    rfl
  | succ n hn =>
    rw [ι_affineSubdivisionMap_succ]
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
      singularSimplexBarycenter, singularSimplexVertices_affineSingularSimplex,
      δ_affineSingularSimplex]
    simp only [← Category.assoc, hn, Preadditive.sum_comp, Preadditive.zsmul_comp,
      ι_affineCone]
    change _ = ∑ p : Fin (n + 2) × BarycentricFlag n, _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [← _root_.SemigroupAction.mul_smul, singularSimplexVertices_affineSingularSimplex]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionMap_pieces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionMap_pieces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionMap_pieces ``Submission.DifferentialGeometry.Homology.affineSubdivisionMap_pieces

end DifferentialGeometry.Homology
