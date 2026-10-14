import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Singular

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u v

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)

local notation "A" => smallSingularSimplices X U


def smallSingularSimplexPushforward {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    TopCat.toSSet.obj (SimplexCategory.toTop.obj ⦋n⦌) ⟶ (A : SSet) :=
  SSet.Subcomplex.lift (TopCat.toSSet.map (singularSimplexMap X σ.val)) (by
    intro m τ hτ
    obtain ⟨ρ, rfl⟩ := hτ
    obtain ⟨i, hi⟩ := σ.property
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨((SimplexCategory.toTop.obj ⦋n⦌).toSSetObjEquiv m ρ z).down, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplexPushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplexPushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplexPushforward ``Submission.DifferentialGeometry.Homology.smallSingularSimplexPushforward


@[reassoc (attr := simp)]
theorem smallSingularSimplexPushforward_ι {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    smallSingularSimplexPushforward X U σ ≫ (A).ι =
      TopCat.toSSet.map (singularSimplexMap X σ.val) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplexPushforward_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplexPushforward_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplexPushforward_ι ``Submission.DifferentialGeometry.Homology.smallSingularSimplexPushforward_ι

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

local notation "KA" => _root_.SSet.chainComplex (A : SSet) R
local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj X) R
local notation "I" => _root_.SSet.chainComplexMap (SSet.Subcomplex.ι (A)) R

private theorem smallPushforward_inclusion {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R ≫ (I) =
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ.val)) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, smallSingularSimplexPushforward_ι]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.smallPushforward_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.smallPushforward_inclusion target :: scope.openDecls } }


def smallSingularSubdivisionMap (n : ℕ) : (KA).X n ⟶ (KA).X n :=
  Sigma.desc (fun σ : (A : SSet) _⦋n⦌ ↦ barycentricSimplexChain R n ≫
    (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionMap ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionMap


@[reassoc]
theorem ι_smallSingularSubdivisionMap {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ smallSingularSubdivisionMap X U R n =
      barycentricSimplexChain R n ≫
        (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f n :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_smallSingularSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_smallSingularSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_smallSingularSubdivisionMap ``Submission.DifferentialGeometry.Homology.ι_smallSingularSubdivisionMap


theorem smallSingularSubdivisionMap_inclusion (n : ℕ) :
    smallSingularSubdivisionMap X U R n ≫ (I).f n =
      (I).f n ≫ singularSubdivisionMap R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSingularSubdivisionMap, Category.assoc,
    ← Category.assoc ((A : SSet).ιChainComplex σ), SSet.ι_chainComplexMap_f,
    ι_singularSubdivisionMap]
  have h := HomologicalComplex.congr_hom (smallPushforward_inclusion X U R σ) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionMap_inclusion ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionMap_inclusion


def smallSingularSubdivisionHomotopyMap (n : ℕ) : (KA).X n ⟶ (KA).X (n + 1) :=
  Sigma.desc (fun σ : (A : SSet) _⦋n⦌ ↦ barycentricSimplexHomotopyChain R n ≫
    (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap


@[reassoc]
theorem ι_smallSingularSubdivisionHomotopyMap {n : ℕ} (σ : (A : SSet) _⦋n⦌) :
    (A : SSet).ιChainComplex σ ≫ smallSingularSubdivisionHomotopyMap X U R n =
      barycentricSimplexHomotopyChain R n ≫
        (SSet.chainComplexMap (smallSingularSimplexPushforward X U σ) R).f (n + 1) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_smallSingularSubdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_smallSingularSubdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_smallSingularSubdivisionHomotopyMap ``Submission.DifferentialGeometry.Homology.ι_smallSingularSubdivisionHomotopyMap


theorem smallSingularSubdivisionHomotopyMap_inclusion (n : ℕ) :
    smallSingularSubdivisionHomotopyMap X U R n ≫ (I).f (n + 1) =
      (I).f n ≫ singularSubdivisionHomotopyMap R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallSingularSubdivisionHomotopyMap, Category.assoc,
    ← Category.assoc ((A : SSet).ιChainComplex σ), SSet.ι_chainComplexMap_f,
    ι_singularSubdivisionHomotopyMap]
  have h := HomologicalComplex.congr_hom (smallPushforward_inclusion X U R σ) (n + 1)
  simp only [HomologicalComplex.comp_f] at h
  rw [h]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_inclusion ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_inclusion

private theorem smallSingularSubdivision_comm (n : ℕ) :
    smallSingularSubdivisionMap X U R (n + 1) ≫ (KA).d (n + 1) n =
      (KA).d (n + 1) n ≫ smallSingularSubdivisionMap X U R n := by
  have : _root_.CategoryTheory.Mono ((I).f n) := mono_smallChainMap_f X U R n
  apply (_root_.CategoryTheory.cancel_mono ((I).f n)).mp
  simp only [Category.assoc]
  rw [← (I).comm, ← Category.assoc, smallSingularSubdivisionMap_inclusion,
    Category.assoc, singularSubdivisionMap_comm, smallSingularSubdivisionMap_inclusion]
  rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
  simp only [Category.assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.smallSingularSubdivision_comm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.smallSingularSubdivision_comm target :: scope.openDecls } }


def smallSingularSubdivision : (KA) ⟶ (KA) where
  f := smallSingularSubdivisionMap X U R
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact smallSingularSubdivision_comm X U R j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivision ``Submission.DifferentialGeometry.Homology.smallSingularSubdivision


@[simp]
theorem smallSingularSubdivision_f (n : ℕ) :
    (smallSingularSubdivision X U R).f n = smallSingularSubdivisionMap X U R n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivision_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivision_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivision_f ``Submission.DifferentialGeometry.Homology.smallSingularSubdivision_f


theorem smallSingularSubdivision_inclusion :
    smallSingularSubdivision X U R ≫ (I) = (I) ≫ singularSubdivision R X := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact smallSingularSubdivisionMap_inclusion X U R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivision_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivision_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivision_inclusion ``Submission.DifferentialGeometry.Homology.smallSingularSubdivision_inclusion

private theorem smallSingularSubdivisionHomotopy_comm (n : ℕ) :
    smallSingularSubdivisionMap X U R (n + 1) - 𝟙 _ =
      (KA).d (n + 1) n ≫ smallSingularSubdivisionHomotopyMap X U R n +
        smallSingularSubdivisionHomotopyMap X U R (n + 1) ≫ (KA).d (n + 2) (n + 1) := by
  have : _root_.CategoryTheory.Mono ((I).f (n + 1)) := mono_smallChainMap_f X U R (n + 1)
  apply (_root_.CategoryTheory.cancel_mono ((I).f (n + 1))).mp
  calc
    _ = (I).f (n + 1) ≫ (singularSubdivisionMap R X (n + 1) - 𝟙 _) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, smallSingularSubdivisionMap_inclusion]
    _ = _ := by
      rw [singularSubdivisionHomotopyMap_comm, Preadditive.comp_add, Preadditive.add_comp]
      simp only [Category.assoc]
      rw [smallSingularSubdivisionHomotopyMap_inclusion]
      rw [← (I).comm, ← Category.assoc (smallSingularSubdivisionHomotopyMap X U R (n + 1)),
        smallSingularSubdivisionHomotopyMap_inclusion]
      rw [← Category.assoc ((KA).d (n + 1) n), ← (I).comm]
      simp only [Category.assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy_comm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy_comm target :: scope.openDecls } }


@[simp]
theorem smallSingularSubdivisionMap_zero : smallSingularSubdivisionMap X U R 0 = 𝟙 _ := by
  have : _root_.CategoryTheory.Mono ((I).f 0) := mono_smallChainMap_f X U R 0
  apply (_root_.CategoryTheory.cancel_mono ((I).f 0)).mp
  rw [smallSingularSubdivisionMap_inclusion, singularSubdivisionMap_zero,
    Category.id_comp, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionMap_zero ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionMap_zero


@[simp]
theorem smallSingularSubdivisionHomotopyMap_zero :
    smallSingularSubdivisionHomotopyMap X U R 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_smallSingularSubdivisionHomotopyMap, barycentricSimplexHomotopyChain_zero,
    _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_zero ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionHomotopyMap_zero


def smallSingularSubdivisionHomotopy : Homotopy (smallSingularSubdivision X U R) (𝟙 (KA)) where
  hom i j := if h : i + 1 = j then
    smallSingularSubdivisionHomotopyMap X U R i ≫ _root_.CategoryTheory.eqToHom (congrArg (KA).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        smallSingularSubdivisionHomotopyMap_zero, _root_.CategoryTheory.Limits.zero_comp, zero_add,
        smallSingularSubdivision_f, smallSingularSubdivisionMap_zero, HomologicalComplex.id_f]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        smallSingularSubdivision_f, HomologicalComplex.id_f]
      exact sub_eq_iff_eq_add.mp (smallSingularSubdivisionHomotopy_comm X U R n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy


@[simp]
theorem smallSingularSubdivisionHomotopy_hom (n : ℕ) :
    (smallSingularSubdivisionHomotopy X U R).hom n (n + 1) =
      smallSingularSubdivisionHomotopyMap X U R n := by
  change (if h : n + 1 = n + 1 then
    smallSingularSubdivisionHomotopyMap X U R n ≫ _root_.CategoryTheory.eqToHom (congrArg (KA).X h) else 0) = _
  rw [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy_hom ``Submission.DifferentialGeometry.Homology.smallSingularSubdivisionHomotopy_hom

end DifferentialGeometry.Homology
