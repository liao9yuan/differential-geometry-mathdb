import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Cone

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

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def singularSimplexBarycenter {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) : E :=
  Finset.univ.centerMass (fun _ : Fin (n + 1) ↦ (1 : ℝ)) (singularSimplexVertices σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexBarycenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexBarycenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexBarycenter ``Submission.DifferentialGeometry.Homology.singularSimplexBarycenter


theorem singularSimplexBarycenter_mem {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, singularSimplexVertices σ i ∈ s) :
    singularSimplexBarycenter σ ∈ s :=
  hs.centerMass_mem (fun _ _ ↦ zero_le_one)
    (by simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
    (fun i _ ↦ hv i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexBarycenter_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexBarycenter_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexBarycenter_mem ``Submission.DifferentialGeometry.Homology.singularSimplexBarycenter_mem

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def affineSubdivisionMap (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n ⟶
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).X n :=
  match n with
  | 0 => 𝟙 _
  | n + 1 => Sigma.desc (fun σ ↦
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫
          affineSubdivisionMap n ≫ affineCone R (singularSimplexBarycenter σ) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionMap ``Submission.DifferentialGeometry.Homology.affineSubdivisionMap


@[simp]
theorem affineSubdivisionMap_zero : affineSubdivisionMap (E := E) R 0 = 𝟙 _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionMap_zero ``Submission.DifferentialGeometry.Homology.affineSubdivisionMap_zero


@[reassoc]
theorem ι_affineSubdivisionMap_succ (n : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫ affineSubdivisionMap R (n + 1) =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex σ ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫
          affineSubdivisionMap R n ≫ affineCone R (singularSimplexBarycenter σ) n :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_affineSubdivisionMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_affineSubdivisionMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_affineSubdivisionMap_succ ``Submission.DifferentialGeometry.Homology.ι_affineSubdivisionMap_succ


theorem affineSubdivisionMap_straightening (n : ℕ) :
    affineSubdivisionMap (E := E) R n ≫
      (SSet.chainComplexMap (affineStraightening (E := E)) R).f n =
        affineSubdivisionMap R n := by
  cases n with
  | zero => rw [affineSubdivisionMap_zero, affineStraightening_f_zero, Category.id_comp]
  | succ n =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc, affineCone_straightening]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionMap_straightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionMap_straightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionMap_straightening ``Submission.DifferentialGeometry.Homology.affineSubdivisionMap_straightening


theorem affineSubdivisionMap_comm (n : ℕ) :
    affineSubdivisionMap (E := E) R (n + 1) ≫
        ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n =
      ((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 1) n ≫
        affineSubdivisionMap R n := by
  induction n with
  | zero =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [affineSubdivisionMap_zero, Category.id_comp, Category.comp_id, Category.assoc]
    rw [affineCone_boundary_zero]
    simp only [Preadditive.comp_sub, Category.comp_id]
    rw [← Category.assoc _ (singularChainAugmentation (E := E) R),
      d_singularChainAugmentation, _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero, sub_zero]
  | succ n hn =>
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, ι_affineSubdivisionMap_succ]
    simp only [Category.assoc]
    rw [eq_sub_of_add_eq (affineCone_boundary R (singularSimplexBarycenter σ) n)]
    simp only [Preadditive.comp_sub, affineSubdivisionMap_straightening]
    rw [← Category.assoc (affineSubdivisionMap R (n + 1)), hn]
    simp only [Category.assoc]
    rw [← Category.assoc
      (((TopCat.toSSet.obj (TopCat.of E)).chainComplex R).d (n + 2) (n + 1))]
    simp only [HomologicalComplex.d_comp_d, _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivisionMap_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivisionMap_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivisionMap_comm ``Submission.DifferentialGeometry.Homology.affineSubdivisionMap_comm

def affineSubdivision :
    (TopCat.toSSet.obj (TopCat.of E)).chainComplex R ⟶
      (TopCat.toSSet.obj (TopCat.of E)).chainComplex R where
  f := affineSubdivisionMap R
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    exact affineSubdivisionMap_comm R j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivision ``Submission.DifferentialGeometry.Homology.affineSubdivision


@[simp]
theorem affineSubdivision_f (n : ℕ) :
    (affineSubdivision (E := E) R).f n = affineSubdivisionMap R n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivision_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivision_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivision_f ``Submission.DifferentialGeometry.Homology.affineSubdivision_f


theorem affineSubdivision_comp_straightening :
    affineSubdivision (E := E) R ≫ SSet.chainComplexMap (affineStraightening (E := E)) R =
      affineSubdivision R := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact affineSubdivisionMap_straightening (E := E) R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSubdivision_comp_straightening then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSubdivision_comp_straightening"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSubdivision_comp_straightening ``Submission.DifferentialGeometry.Homology.affineSubdivision_comp_straightening

end DifferentialGeometry.Homology
