import Submission.DifferentialGeometry.Topology.Homology.SingularSubcomplex
import Submission.DifferentialGeometry.Topology.Homology.Subdivision.DiameterBound

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.AlgebraicTopology _root_.Submission.DifferentialGeometry.MathlibCompat
open scoped _root_.Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

open _root_.Submission.DifferentialGeometry.Topology.SingularPair.AffChain

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u})

lemma subdivisionHomotopyComponent_d_zero : subdivisionHomotopyComponent R X 0 ≫ (simplicialChains R X).d 1 0 + (barycentricSubdivisionMap R X).f 0 = 𝟙 _ := by
  have h := (homotopyIdBarycentricSubdivision R X).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [homotopyIdBarycentricSubdivision, dif_pos rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, zero_add, HomologicalComplex.id_f] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_d_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_d_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_d_zero ``Submission.DifferentialGeometry.Topology.SingularPair.subdivisionHomotopyComponent_d_zero

lemma d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d (j : ℕ) :
    (simplicialChains R X).d (j + 1) j ≫ subdivisionHomotopyComponent R X j + subdivisionHomotopyComponent R X (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
      (barycentricSubdivisionMap R X).f (j + 1) = 𝟙 _ := by
  have h := (homotopyIdBarycentricSubdivision R X).comm (j + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  simp only [homotopyIdBarycentricSubdivision, dif_pos rfl, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.comp_id, HomologicalComplex.id_f] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d ``Submission.DifferentialGeometry.Topology.SingularPair.d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d

def iteratedSubdivisionHomotopyComponent (k j : ℕ) : (simplicialChains R X).X j ⟶ (simplicialChains R X).X (j + 1) :=
  ∑ i ∈ Finset.range k, (iteratedBarycentricSubdivisionMap R X i).f j ≫ subdivisionHomotopyComponent R X j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent

@[simp] lemma iteratedSubdivisionHomotopyComponent_zero (j : ℕ) : iteratedSubdivisionHomotopyComponent R X 0 j = 0 := by simp [iteratedSubdivisionHomotopyComponent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_zero ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_zero

lemma iteratedSubdivisionHomotopyComponent_succ (k j : ℕ) : iteratedSubdivisionHomotopyComponent R X (k + 1) j = iteratedSubdivisionHomotopyComponent R X k j + (iteratedBarycentricSubdivisionMap R X k).f j ≫ subdivisionHomotopyComponent R X j := by
  simp [iteratedSubdivisionHomotopyComponent, Finset.sum_range_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_succ ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_succ

lemma iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent {k k' : ℕ} (h : k' ≤ k) (j : ℕ) :
    iteratedSubdivisionHomotopyComponent R X k j - iteratedSubdivisionHomotopyComponent R X k' j = ∑ i ∈ Finset.Ico k' k, (iteratedBarycentricSubdivisionMap R X i).f j ≫ subdivisionHomotopyComponent R X j := by
  rw [sub_eq_iff_eq_add', iteratedSubdivisionHomotopyComponent, iteratedSubdivisionHomotopyComponent, Finset.sum_range_add_sum_Ico _ h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent

lemma iteratedSubdivisionHomotopyComponent_d_zero (k : ℕ) : iteratedSubdivisionHomotopyComponent R X k 0 ≫ (simplicialChains R X).d 1 0 + (iteratedBarycentricSubdivisionMap R X k).f 0 = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedSubdivisionHomotopyComponent_succ, Preadditive.add_comp, iteratedBarycentricSubdivisionMap_succ, HomologicalComplex.comp_f, Category.assoc,
      add_assoc, ← Preadditive.comp_add, subdivisionHomotopyComponent_d_zero, Category.comp_id, ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_d_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_d_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_d_zero ``Submission.DifferentialGeometry.Topology.SingularPair.iteratedSubdivisionHomotopyComponent_d_zero

lemma d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d (k j : ℕ) :
    (simplicialChains R X).d (j + 1) j ≫ iteratedSubdivisionHomotopyComponent R X k j + iteratedSubdivisionHomotopyComponent R X k (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
      (iteratedBarycentricSubdivisionMap R X k).f (j + 1) = 𝟙 _ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedSubdivisionHomotopyComponent_succ, iteratedSubdivisionHomotopyComponent_succ, Preadditive.add_comp, Preadditive.comp_add, iteratedBarycentricSubdivisionMap_succ,
      HomologicalComplex.comp_f, Category.assoc,
      ← (iteratedBarycentricSubdivisionMap R X k).comm_assoc (j + 1) j]
    have key : (iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ ((simplicialChains R X).d (j + 1) j ≫ subdivisionHomotopyComponent R X j +
        subdivisionHomotopyComponent R X (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) + (barycentricSubdivisionMap R X).f (j + 1)) =
        (iteratedBarycentricSubdivisionMap R X k).f (j + 1) := by
      rw [d_subdivisionHomotopyComponent_add_subdivisionHomotopyComponent_d, Category.comp_id]
    simp only [Preadditive.comp_add] at key
    calc _ = ((simplicialChains R X).d (j + 1) j ≫ iteratedSubdivisionHomotopyComponent R X k j +
          iteratedSubdivisionHomotopyComponent R X k (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
          (iteratedBarycentricSubdivisionMap R X k).f (j + 1)) - (iteratedBarycentricSubdivisionMap R X k).f (j + 1) +
          ((iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ (simplicialChains R X).d (j + 1) j ≫ subdivisionHomotopyComponent R X j +
            (iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ subdivisionHomotopyComponent R X (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) +
            (iteratedBarycentricSubdivisionMap R X k).f (j + 1) ≫ (barycentricSubdivisionMap R X).f (j + 1)) := by abel
      _ = 𝟙 _ := by rw [ih, key, sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d ``Submission.DifferentialGeometry.Topology.SingularPair.d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d

section cover

variable {X} {ι : Type*} (U : ι → Set X)

abbrev smallInc :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R ⟶ simplicialChains R X :=
  SSet.chainComplexMap (small X U).ι R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallInc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallInc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallInc ``Submission.DifferentialGeometry.Topology.SingularPair.smallInc

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSmallInc (n : ℕ) : _root_.CategoryTheory.Mono ((smallInc R U).f n) :=
  inferInstanceAs (_root_.CategoryTheory.Mono ((SSet.chainComplexMap (small X U).pair.hom R).f n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSmallInc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSmallInc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSmallInc ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntFNatSmallInc

@[reassoc]
lemma ι_smallInc_f {n : ℕ}
    (σ : ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}) _⦋n⦌) :
    ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).ιChainComplex σ ≫
      (smallInc R U).f n = (TopCat.toSSet.obj X).ιChainComplex σ.1 :=
  SSet.ι_chainComplexMap_f _ _ (small X U).ι R σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_smallInc_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_smallInc_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_smallInc_f ``Submission.DifferentialGeometry.Topology.SingularPair.ι_smallInc_f

variable (hU : ⋃ i, interior (U i) = Set.univ)

open _root_.Classical in
def mIdx {m : ℕ} (τ : Sing X m) : ℕ :=
  Nat.find (exists_isSmall hU (X.toSSetObjEquiv _ τ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mIdx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mIdx ``Submission.DifferentialGeometry.Topology.SingularPair.mIdx

lemma isSmall_mIdx {m : ℕ} (τ : Sing X m) :
    isSmall U (X.toSSetObjEquiv _ τ) (mIdx U hU τ) := by
  classical exact Nat.find_spec (exists_isSmall hU (X.toSSetObjEquiv _ τ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isSmall_mIdx then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isSmall_mIdx"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isSmall_mIdx ``Submission.DifferentialGeometry.Topology.SingularPair.isSmall_mIdx

lemma mIdx_le {m : ℕ} (τ : Sing X m) {k : ℕ} (h : isSmall U (X.toSSetObjEquiv _ τ) k) :
    mIdx U hU τ ≤ k := by
  classical exact Nat.find_min' (exists_isSmall hU (X.toSSetObjEquiv _ τ)) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mIdx_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mIdx_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mIdx_le ``Submission.DifferentialGeometry.Topology.SingularPair.mIdx_le

lemma mIdx_δ_le {m : ℕ} (τ : Sing X (m + 1)) (i : Fin (m + 2)) :
    mIdx U hU ((TopCat.toSSet.obj X).δ i τ) ≤ mIdx U hU τ :=
  mIdx_le U hU _ ((isSmall_mIdx U hU τ).δ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mIdx_δ_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mIdx_δ_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mIdx_δ_le ``Submission.DifferentialGeometry.Topology.SingularPair.mIdx_δ_le

lemma isSmall_zero_of_mem_small {m : ℕ} {τ : Sing X m} (hτ : τ ∈ (small X U).obj _) :
    isSmall U (X.toSSetObjEquiv _ τ) 0 := by
  obtain ⟨i, hi⟩ := (mem_small_iff U τ).1 hτ
  intro s _
  exact ⟨i, (Set.image_subset_range _ _).trans hi⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isSmall_zero_of_mem_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isSmall_zero_of_mem_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isSmall_zero_of_mem_small ``Submission.DifferentialGeometry.Topology.SingularPair.isSmall_zero_of_mem_small

lemma mIdx_eq_zero_of_mem_small {m : ℕ} {τ : Sing X m} (hτ : τ ∈ (small X U).obj _) :
    mIdx U hU τ = 0 :=
  Nat.le_zero.1 (mIdx_le U hU τ (isSmall_zero_of_mem_small U hτ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mIdx_eq_zero_of_mem_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mIdx_eq_zero_of_mem_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mIdx_eq_zero_of_mem_small ``Submission.DifferentialGeometry.Topology.SingularPair.mIdx_eq_zero_of_mem_small

lemma δ_mem_small {m : ℕ} {τ : Sing X (m + 1)} (hτ : τ ∈ (small X U).obj _)
    (i : Fin (m + 2)) :
    (TopCat.toSSet.obj X).δ i τ ∈ (small X U).obj _ :=
  (small X U).map _ hτ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ_mem_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ_mem_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ_mem_small ``Submission.DifferentialGeometry.Topology.SingularPair.δ_mem_small

def smallSubdivisionHomotopyComponent (j : ℕ) : (simplicialChains R X).X j ⟶ (simplicialChains R X).X (j + 1) :=
  Sigma.desc fun τ => (TopCat.toSSet.obj X).ιChainComplex τ ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyComponent

@[reassoc]
lemma ι_smallSubdivisionHomotopyComponent {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ smallSubdivisionHomotopyComponent R U hU j =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_smallSubdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_smallSubdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_smallSubdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.ι_smallSubdivisionHomotopyComponent

lemma ι_d_smallSubdivisionHomotopyComponent {j : ℕ} (τ : Sing X (j + 1)) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (simplicialChains R X).d (j + 1) j ≫ smallSubdivisionHomotopyComponent R U hU j =
      ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i τ) ≫
          iteratedSubdivisionHomotopyComponent R X (mIdx U hU ((TopCat.toSSet.obj X).δ i τ)) j) := by
  rw [SSet.ιChainComplex_d_assoc, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, ι_smallSubdivisionHomotopyComponent]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_d_smallSubdivisionHomotopyComponent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_d_smallSubdivisionHomotopyComponent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_d_smallSubdivisionHomotopyComponent ``Submission.DifferentialGeometry.Topology.SingularPair.ι_d_smallSubdivisionHomotopyComponent

def smallSubdivisionHomotopyHom (i j : ℕ) : (simplicialChains R X).X i ⟶ (simplicialChains R X).X j :=
  if h : i + 1 = j then smallSubdivisionHomotopyComponent R U hU i ≫ ((simplicialChains R X).XIsoOfEq h).hom else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom ``Submission.DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom

lemma smallSubdivisionHomotopyHom_succ (i : ℕ) : smallSubdivisionHomotopyHom R U hU i (i + 1) = smallSubdivisionHomotopyComponent R U hU i := by
  simp [smallSubdivisionHomotopyHom]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom_succ ``Submission.DifferentialGeometry.Topology.SingularPair.smallSubdivisionHomotopyHom_succ

abbrev smallSubdivisionNullHomotopicMap : simplicialChains R X ⟶ simplicialChains R X := Homotopy.nullHomotopicMap (smallSubdivisionHomotopyHom R U hU)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap ``Submission.DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap

lemma smallSubdivisionNullHomotopicMap_f_zero : (smallSubdivisionNullHomotopicMap R U hU).f 0 = smallSubdivisionHomotopyComponent R U hU 0 ≫ (simplicialChains R X).d 1 0 := by
  change dNext 0 (smallSubdivisionHomotopyHom R U hU) + prevD 0 (smallSubdivisionHomotopyHom R U hU) = _
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, smallSubdivisionHomotopyHom_succ, zero_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_zero ``Submission.DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_zero

lemma smallSubdivisionNullHomotopicMap_f_succ (j : ℕ) : (smallSubdivisionNullHomotopicMap R U hU).f (j + 1) =
    (simplicialChains R X).d (j + 1) j ≫ smallSubdivisionHomotopyComponent R U hU j +
      smallSubdivisionHomotopyComponent R U hU (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) := by
  change dNext (j + 1) (smallSubdivisionHomotopyHom R U hU) + prevD (j + 1) (smallSubdivisionHomotopyHom R U hU) = _
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, smallSubdivisionHomotopyHom_succ, smallSubdivisionHomotopyHom_succ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_succ ``Submission.DifferentialGeometry.Topology.SingularPair.smallSubdivisionNullHomotopicMap_f_succ

abbrev ρbig : simplicialChains R X ⟶ simplicialChains R X := 𝟙 _ - smallSubdivisionNullHomotopicMap R U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ρbig then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ρbig"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ρbig ``Submission.DifferentialGeometry.Topology.SingularPair.ρbig

lemma ι_ρbig_zero (τ : Sing X 0) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f 0 =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f 0 := by
  have hD : iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) 0 ≫ (simplicialChains R X).d 1 0 =
      𝟙 _ - (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f 0 := by
    rw [← iteratedSubdivisionHomotopyComponent_d_zero R X (mIdx U hU τ)]; abel
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, smallSubdivisionNullHomotopicMap_f_zero, Preadditive.comp_sub,
    Category.comp_id, ι_smallSubdivisionHomotopyComponent_assoc, hD, Preadditive.comp_sub, Category.comp_id, sub_sub_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_ρbig_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_ρbig_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_ρbig_zero ``Submission.DifferentialGeometry.Topology.SingularPair.ι_ρbig_zero

lemma ι_ρbig_succ {j : ℕ} (τ : Sing X (j + 1)) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f (j + 1) =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f (j + 1) +
      ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        ((TopCat.toSSet.obj X).δ i τ) ≫
          (iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j - iteratedSubdivisionHomotopyComponent R X (mIdx U hU ((TopCat.toSSet.obj X).δ i τ)) j)) := by
  have hD : iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) (j + 1) ≫ (simplicialChains R X).d (j + 2) (j + 1) =
      𝟙 _ - (simplicialChains R X).d (j + 1) j ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j -
        (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f (j + 1) := by
    rw [← d_iteratedSubdivisionHomotopyComponent_add_iteratedSubdivisionHomotopyComponent_d R X (mIdx U hU τ) j]; abel
  have h2 : (TopCat.toSSet.obj X).ιChainComplex τ ≫ smallSubdivisionHomotopyComponent R U hU (j + 1) ≫
      (simplicialChains R X).d (j + 2) (j + 1) =
      (TopCat.toSSet.obj X).ιChainComplex τ -
        ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
          ((TopCat.toSSet.obj X).δ i τ) ≫ iteratedSubdivisionHomotopyComponent R X (mIdx U hU τ) j) -
        (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X (mIdx U hU τ)).f (j + 1) := by
    rw [ι_smallSubdivisionHomotopyComponent_assoc, hD, Preadditive.comp_sub, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp]
  rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, smallSubdivisionNullHomotopicMap_f_succ, Preadditive.comp_sub,
    Category.comp_id, Preadditive.comp_add, ι_d_smallSubdivisionHomotopyComponent, h2]
  simp only [Preadditive.comp_sub, smul_sub, Finset.sum_sub_distrib]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_ρbig_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_ρbig_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_ρbig_succ ``Submission.DifferentialGeometry.Topology.SingularPair.ι_ρbig_succ

lemma ι_ρbig_of_mem_small {j : ℕ} {τ : Sing X j} (hτ : τ ∈ (small X U).obj _) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j =
      (TopCat.toSSet.obj X).ιChainComplex τ := by
  cases j with
  | zero =>
    rw [ι_ρbig_zero, mIdx_eq_zero_of_mem_small U hU hτ, iteratedBarycentricSubdivisionMap_zero, HomologicalComplex.id_f,
      Category.comp_id]
  | succ j =>
    rw [ι_ρbig_succ, mIdx_eq_zero_of_mem_small U hU hτ, iteratedBarycentricSubdivisionMap_zero, HomologicalComplex.id_f,
      Category.comp_id]
    simp only [mIdx_eq_zero_of_mem_small U hU (δ_mem_small U hτ _), sub_self, Limits.comp_zero,
      smul_zero, Finset.sum_const_zero, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_ρbig_of_mem_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_ρbig_of_mem_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_ρbig_of_mem_small ``Submission.DifferentialGeometry.Topology.SingularPair.ι_ρbig_of_mem_small

def smallRange (j : ℕ) : AddSubgroup (R ⟶ (simplicialChains R X).X j) :=
  (Preadditive.rightComp R ((smallInc R U).f j)).range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallRange ``Submission.DifferentialGeometry.Topology.SingularPair.smallRange

lemma mem_smallRange_iff {j : ℕ} (f : R ⟶ (simplicialChains R X).X j) :
    f ∈ smallRange R U j ↔
      ∃ c : R ⟶
        (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R).X j,
        c ≫ (smallInc R U).f j = f :=
  AddMonoidHom.mem_range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mem_smallRange_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mem_smallRange_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mem_smallRange_iff ``Submission.DifferentialGeometry.Topology.SingularPair.mem_smallRange_iff

lemma ι_iteratedBarycentricSubdivisionMap_mem_smallRange {m : ℕ} (τ : Sing X m) {k : ℕ}
    (h : isSmall U (X.toSSetObjEquiv _ τ) k) {j : ℕ} (hj : k ≤ j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X j).f m ∈ smallRange R U m := by
  rw [mem_smallRange_iff, ← sing_toSSetObjEquiv τ,
    h.ι_iteratedBarycentricSubdivisionMap_f_eq R hj (small X U) (singSub_le_small U)]
  exact ⟨_, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_mem_smallRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_mem_smallRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_mem_smallRange ``Submission.DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_mem_smallRange

lemma ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange {m : ℕ} (τ : Sing X m) {k : ℕ}
    (h : isSmall U (X.toSSetObjEquiv _ τ) k) {j : ℕ} (hj : k ≤ j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (iteratedBarycentricSubdivisionMap R X j).f m ≫ subdivisionHomotopyComponent R X m ∈
      smallRange R U (m + 1) := by
  rw [mem_smallRange_iff, ← sing_toSSetObjEquiv τ,
    h.ι_iteratedBarycentricSubdivisionMap_f_subdivisionHomotopyComponent_eq R hj (small X U) (singSub_le_small U)]
  exact ⟨_, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange ``Submission.DifferentialGeometry.Topology.SingularPair.ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange

lemma ι_ρbig_mem_smallRange {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j ∈ smallRange R U j := by
  cases j with
  | zero =>
    rw [ι_ρbig_zero]
    exact ι_iteratedBarycentricSubdivisionMap_mem_smallRange R U τ (isSmall_mIdx U hU τ) le_rfl
  | succ j =>
    rw [ι_ρbig_succ]
    refine _root_.AddMemClass.add_mem (ι_iteratedBarycentricSubdivisionMap_mem_smallRange R U τ (isSmall_mIdx U hU τ) le_rfl)
      (sum_mem fun i _ => zsmul_mem ?_ _)
    rw [iteratedSubdivisionHomotopyComponent_sub_iteratedSubdivisionHomotopyComponent R X (mIdx_δ_le U hU τ i), Preadditive.comp_sum]
    refine sum_mem fun i' hi' => ?_
    exact ι_iteratedBarycentricSubdivisionMap_subdivisionHomotopyComponent_mem_smallRange R U _ (isSmall_mIdx U hU _) (Finset.mem_Ico.1 hi').1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_ρbig_mem_smallRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_ρbig_mem_smallRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_ρbig_mem_smallRange ``Submission.DifferentialGeometry.Topology.SingularPair.ι_ρbig_mem_smallRange

def ρf (j : ℕ) :
    (simplicialChains R X).X j ⟶
      (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R).X j :=
  Sigma.desc fun τ => ((mem_smallRange_iff R U _).1 (ι_ρbig_mem_smallRange R U hU τ)).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ρf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ρf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ρf ``Submission.DifferentialGeometry.Topology.SingularPair.ρf

lemma ι_ρf_comp {j : ℕ} (τ : Sing X j) :
    (TopCat.toSSet.obj X).ιChainComplex τ ≫ ρf R U hU j ≫ (smallInc R U).f j =
      (TopCat.toSSet.obj X).ιChainComplex τ ≫ (ρbig R U hU).f j := by
  rw [← Category.assoc]
  erw [Sigma.ι_desc]
  exact ((mem_smallRange_iff R U _).1 (ι_ρbig_mem_smallRange R U hU τ)).choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_ρf_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_ρf_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_ρf_comp ``Submission.DifferentialGeometry.Topology.SingularPair.ι_ρf_comp

lemma ρf_comp_smallChainMap_f (j : ℕ) :
    ρf R U hU j ≫ (smallInc R U).f j = (ρbig R U hU).f j :=
  SSet.chainComplex_hom_ext fun τ => ι_ρf_comp R U hU τ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ρf_comp_smallChainMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ρf_comp_smallChainMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ρf_comp_smallChainMap_f ``Submission.DifferentialGeometry.Topology.SingularPair.ρf_comp_smallChainMap_f

def ρ : simplicialChains R X ⟶ ((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R where
  f j := ρf R U hU j
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [← _root_.CategoryTheory.cancel_mono ((smallInc R U).f j), Category.assoc, Category.assoc,
      ← (smallInc R U).comm (j + 1) j, ← Category.assoc, ρf_comp_smallChainMap_f,
      ρf_comp_smallChainMap_f, (ρbig R U hU).comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ρ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ρ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ρ ``Submission.DifferentialGeometry.Topology.SingularPair.ρ

@[simp] lemma ρ_f (j : ℕ) : (ρ R U hU).f j = ρf R U hU j := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ρ_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ρ_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ρ_f ``Submission.DifferentialGeometry.Topology.SingularPair.ρ_f

theorem ρ_comp_smallChainMap : ρ R U hU ≫ smallInc R U = ρbig R U hU :=
  HomologicalComplex.hom_ext _ _ fun j => ρf_comp_smallChainMap_f R U hU j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ρ_comp_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ρ_comp_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ρ_comp_smallChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.ρ_comp_smallChainMap

theorem smallChainMap_comp_ρ : smallInc R U ≫ ρ R U hU = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [← _root_.CategoryTheory.cancel_mono ((smallInc R U).f j), Category.assoc, Category.assoc, ρ_f,
    ρf_comp_smallChainMap_f, Category.comp_id, ι_smallInc_f_assoc,
    ι_ρbig_of_mem_small R U hU σ.2, ι_smallInc_f]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallChainMap_comp_ρ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallChainMap_comp_ρ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallChainMap_comp_ρ ``Submission.DifferentialGeometry.Topology.SingularPair.smallChainMap_comp_ρ

def homotopyρ : Homotopy (ρ R U hU ≫ smallInc R U) (𝟙 (simplicialChains R X)) where
  hom := -smallSubdivisionHomotopyHom R U hU
  zero i j hij := by
    have : ¬ i + 1 = j := hij
    simp [smallSubdivisionHomotopyHom, this]
  comm i := by
    rw [ρ_comp_smallChainMap, map_neg, map_neg, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f]
    change 𝟙 _ - (dNext i (smallSubdivisionHomotopyHom R U hU) + prevD i (smallSubdivisionHomotopyHom R U hU)) = _
    abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homotopyρ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homotopyρ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homotopyρ ``Submission.DifferentialGeometry.Topology.SingularPair.homotopyρ

def smallHomotopyEquiv :
    HomotopyEquiv (((small X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).chainComplex R)
      (simplicialChains R X) where
  hom := smallInc R U
  inv := ρ R U hU
  homotopyHomInvId := Homotopy.ofEq (smallChainMap_comp_ρ R U hU)
  homotopyInvHomId := homotopyρ R U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv

@[simp] lemma smallHomotopyEquiv_hom : (smallHomotopyEquiv R U hU).hom = smallInc R U := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv_hom ``Submission.DifferentialGeometry.Topology.SingularPair.smallHomotopyEquiv_hom

include hU in
theorem quasiIso_smallChainMap : QuasiIso (SSet.chainComplexMap (small X U).ι R) :=
  (smallHomotopyEquiv R U hU).quasiIso_hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap

include hU in
theorem quasiIso_smallChainMap' : QuasiIso (smallChainMap X R U) :=
  quasiIso_smallChainMap R U hU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap' ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIso_smallChainMap'

include hU in
theorem quasiIsoAt_smallChainMap (n : ℕ) :
    QuasiIsoAt (SSet.chainComplexMap (small X U).ι R) n :=
  (smallHomotopyEquiv R U hU).quasiIsoAt_hom n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIsoAt_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIsoAt_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIsoAt_smallChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIsoAt_smallChainMap

include hU in
theorem isIso_homologyMap_smallChainMap (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (SSet.chainComplexMap (small X U).ι R) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 (quasiIsoAt_smallChainMap R U hU n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_smallChainMap ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_smallChainMap

include hU in
theorem isIso_homologyMap_small (n : ℕ) :
    IsIso (SSet.homologyMap (small X U).ι R n) :=
  isIso_homologyMap_smallChainMap R U hU n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_small ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_small

end cover

end DifferentialGeometry.Topology.SingularPair
