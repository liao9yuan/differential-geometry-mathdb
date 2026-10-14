import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Universal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial _root_.AlgebraicTopology

universe u

namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k) (X : TopCat.{u})


def singularSimplexMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    SimplexCategory.toTop.obj ⦋n⦌ ⟶ X := σ.down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexMap ``Submission.DifferentialGeometry.Homology.singularSimplexMap

local notation "K" => _root_.SSet.chainComplex (TopCat.toSSet.obj X) R


@[reassoc]
theorem fundamentalSimplexChain_pushforward {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    fundamentalSimplexChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  rw [fundamentalSimplexChain, SSet.ι_chainComplexMap_f]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.fundamentalSimplexChain_pushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.fundamentalSimplexChain_pushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.fundamentalSimplexChain_pushforward ``Submission.DifferentialGeometry.Homology.fundamentalSimplexChain_pushforward

private theorem pushforward_face {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n + 1⦌)
    (i : Fin (n + 2)) :
    SSet.chainComplexMap (TopCat.toSSet.map
        (SimplexCategory.toTop.map (SimplexCategory.δ i))) R ≫
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R =
      SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X ((TopCat.toSSet.obj X).δ i σ))) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← TopCat.toSSet.map_comp]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.pushforward_face
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.pushforward_face target :: scope.openDecls } }


def singularSubdivisionMap (n : ℕ) : (K).X n ⟶ (K).X n :=
  Sigma.desc (fun σ : TopCat.toSSet.obj X _⦋n⦌ ↦ barycentricSimplexChain R n ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionMap ``Submission.DifferentialGeometry.Homology.singularSubdivisionMap


@[reassoc]
theorem ι_singularSubdivisionMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSubdivisionMap R X n =
      barycentricSimplexChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f n :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_singularSubdivisionMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_singularSubdivisionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_singularSubdivisionMap ``Submission.DifferentialGeometry.Homology.ι_singularSubdivisionMap


@[simp]
theorem singularSubdivisionMap_zero : singularSubdivisionMap R X 0 = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularSubdivisionMap, barycentricSimplexChain_zero,
    fundamentalSimplexChain_pushforward, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionMap_zero ``Submission.DifferentialGeometry.Homology.singularSubdivisionMap_zero


theorem singularSubdivisionMap_comm (n : ℕ) :
    singularSubdivisionMap R X (n + 1) ≫ (K).d (n + 1) n =
      (K).d (n + 1) n ≫ singularSubdivisionMap R X n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionMap, Category.assoc,
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).comm, ← Category.assoc, barycentricSimplexChain_boundary]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ), SSet.ιChainComplex_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    ι_singularSubdivisionMap]
  apply Finset.sum_congr rfl
  intro i _
  have h := HomologicalComplex.congr_hom (pushforward_face R X σ i) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionMap_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionMap_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionMap_comm ``Submission.DifferentialGeometry.Homology.singularSubdivisionMap_comm


def singularSubdivision : (K) ⟶ (K) where
  f := singularSubdivisionMap R X
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst i
    exact singularSubdivisionMap_comm R X j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivision ``Submission.DifferentialGeometry.Homology.singularSubdivision


@[simp]
theorem singularSubdivision_f (n : ℕ) :
    (singularSubdivision R X).f n = singularSubdivisionMap R X n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivision_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivision_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivision_f ``Submission.DifferentialGeometry.Homology.singularSubdivision_f


def singularSubdivisionHomotopyMap (n : ℕ) : (K).X n ⟶ (K).X (n + 1) :=
  Sigma.desc (fun σ : TopCat.toSSet.obj X _⦋n⦌ ↦ barycentricSimplexHomotopyChain R n ≫
    (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap ``Submission.DifferentialGeometry.Homology.singularSubdivisionHomotopyMap


@[reassoc]
theorem ι_singularSubdivisionHomotopyMap {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSubdivisionHomotopyMap R X n =
      barycentricSimplexHomotopyChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).f (n + 1) :=
  Sigma.ι_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_singularSubdivisionHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_singularSubdivisionHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_singularSubdivisionHomotopyMap ``Submission.DifferentialGeometry.Homology.ι_singularSubdivisionHomotopyMap


@[simp]
theorem singularSubdivisionHomotopyMap_zero : singularSubdivisionHomotopyMap R X 0 = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [ι_singularSubdivisionHomotopyMap, barycentricSimplexHomotopyChain_zero,
    _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_zero ``Submission.DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_zero


theorem singularSubdivisionHomotopyMap_comm (n : ℕ) :
    singularSubdivisionMap R X (n + 1) - 𝟙 _ =
      (K).d (n + 1) n ≫ singularSubdivisionHomotopyMap R X n +
        singularSubdivisionHomotopyMap R X (n + 1) ≫ (K).d (n + 2) (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Preadditive.comp_sub, ι_singularSubdivisionMap, Category.comp_id,
    ← fundamentalSimplexChain_pushforward R X σ, ← Preadditive.sub_comp,
    barycentricSimplexHomotopyChain_boundary, Preadditive.add_comp, Preadditive.comp_add,
    fundamentalSimplexChain_pushforward]
  congr 1
  · rw [← Category.assoc, SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
      ι_singularSubdivisionHomotopyMap]
    apply Finset.sum_congr rfl
    intro i _
    have h := HomologicalComplex.congr_hom (pushforward_face R X σ i) (n + 1)
    simp only [HomologicalComplex.comp_f] at h
    rw [h]
  · rw [Category.assoc, ← (SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R).comm]
    rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
      ι_singularSubdivisionHomotopyMap, Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_comm ``Submission.DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_comm


def singularSubdivisionHomotopy : Homotopy (singularSubdivision R X) (𝟙 (K)) where
  hom i j := if h : i + 1 = j then
    singularSubdivisionHomotopyMap R X i ≫ _root_.CategoryTheory.eqToHom (congrArg (K).X h) else 0
  zero i j hij := by
    change ¬ i + 1 = j at hij
    exact dif_neg hij
  comm n := by
    cases n with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        singularSubdivisionHomotopyMap_zero, _root_.CategoryTheory.Limits.zero_comp, zero_add,
        singularSubdivision_f, singularSubdivisionMap_zero, HomologicalComplex.id_f]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simp only [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id,
        singularSubdivision_f, HomologicalComplex.id_f]
      exact sub_eq_iff_eq_add.mp (singularSubdivisionHomotopyMap_comm R X n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionHomotopy ``Submission.DifferentialGeometry.Homology.singularSubdivisionHomotopy


@[simp]
theorem singularSubdivisionHomotopy_hom (n : ℕ) :
    (singularSubdivisionHomotopy R X).hom n (n + 1) =
      singularSubdivisionHomotopyMap R X n := by
  change (if h : n + 1 = n + 1 then
    singularSubdivisionHomotopyMap R X n ≫ _root_.CategoryTheory.eqToHom (congrArg (K).X h) else 0) = _
  rw [dif_pos rfl, _root_.CategoryTheory.eqToHom_refl, Category.comp_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionHomotopy_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionHomotopy_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionHomotopy_hom ``Submission.DifferentialGeometry.Homology.singularSubdivisionHomotopy_hom

variable {Y : TopCat.{u}} (f : X ⟶ Y)


theorem singularSimplexMap_naturality {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularSimplexMap Y ((TopCat.toSSet.map f).app (_root_.Opposite.op ⦋n⦌) σ) =
      singularSimplexMap X σ ≫ f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexMap_naturality ``Submission.DifferentialGeometry.Homology.singularSimplexMap_naturality

private theorem pushforward_postcomp {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    SSet.chainComplexMap (TopCat.toSSet.map (singularSimplexMap X σ)) R ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (singularSimplexMap Y ((TopCat.toSSet.map f).app (_root_.Opposite.op ⦋n⦌) σ))) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← TopCat.toSSet.map_comp, singularSimplexMap_naturality]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.pushforward_postcomp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.pushforward_postcomp target :: scope.openDecls } }


theorem singularSubdivisionMap_naturality (n : ℕ) :
    singularSubdivisionMap R X n ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫ singularSubdivisionMap R Y n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionMap, Category.assoc]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
    SSet.ι_chainComplexMap_f, ι_singularSubdivisionMap]
  have h := HomologicalComplex.congr_hom (pushforward_postcomp R X f σ) n
  simp only [HomologicalComplex.comp_f] at h
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionMap_naturality ``Submission.DifferentialGeometry.Homology.singularSubdivisionMap_naturality


theorem singularSubdivision_naturality :
    singularSubdivision R X ≫ SSet.chainComplexMap (TopCat.toSSet.map f) R =
      SSet.chainComplexMap (TopCat.toSSet.map f) R ≫ singularSubdivision R Y := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact singularSubdivisionMap_naturality R X f n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivision_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivision_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivision_naturality ``Submission.DifferentialGeometry.Homology.singularSubdivision_naturality


theorem singularSubdivisionHomotopyMap_naturality (n : ℕ) :
    singularSubdivisionHomotopyMap R X n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) R).f (n + 1) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) R).f n ≫
        singularSubdivisionHomotopyMap R Y n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_singularSubdivisionHomotopyMap, Category.assoc]
  rw [← Category.assoc ((TopCat.toSSet.obj X).ιChainComplex σ),
    SSet.ι_chainComplexMap_f, ι_singularSubdivisionHomotopyMap]
  have h := HomologicalComplex.congr_hom (pushforward_postcomp R X f σ) (n + 1)
  simp only [HomologicalComplex.comp_f] at h
  rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_naturality ``Submission.DifferentialGeometry.Homology.singularSubdivisionHomotopyMap_naturality

end DifferentialGeometry.Homology
