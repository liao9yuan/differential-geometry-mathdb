import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SingularHomology.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial _root_.AlgebraicTopology

universe u v w

namespace DifferentialGeometry.Homology

variable (X : TopCat.{u}) {ι : Type v} (U : ι → Set X)


def smallSingularSimplices : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i}
  map f σ h := by
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨stdSimplex.map f.unop z, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices ``Submission.DifferentialGeometry.Homology.smallSingularSimplices


theorem mem_smallSingularSimplices_iff {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingularSimplices X U).obj n ↔
      ∃ i, Set.range (X.toSSetObjEquiv n σ) ⊆ U i := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.mem_smallSingularSimplices_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.mem_smallSingularSimplices_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.mem_smallSingularSimplices_iff ``Submission.DifferentialGeometry.Homology.mem_smallSingularSimplices_iff

theorem smallSingularSimplices_eq_iSup_range :
    smallSingularSimplices X U =
      ⨆ i, SSet.Subcomplex.range
        (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
          C(U i, X)))) := by
  ext n σ
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj,
    Set.mem_range, mem_smallSingularSimplices_iff]
  constructor
  · rintro ⟨i, hi⟩
    let τ : C(stdSimplex ℝ (Fin (n.unop.len + 1)), U i) :=
      ⟨fun z ↦ ⟨X.toSSetObjEquiv n σ z, hi ⟨z, rfl⟩⟩,
        (X.toSSetObjEquiv n σ).continuous.subtype_mk _⟩
    refine ⟨i, ((TopCat.of (U i)).toSSetObjEquiv n).symm τ, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext z
    rfl
  · rintro ⟨i, τ, rfl⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (((TopCat.of (U i)).toSSetObjEquiv n) τ z).property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices_eq_iSup_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices_eq_iSup_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices_eq_iSup_range ``Submission.DifferentialGeometry.Homology.smallSingularSimplices_eq_iSup_range


theorem smallSingularSimplices_le {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallSingularSimplices X U ≤ smallSingularSimplices X V := by
  intro n σ hσ
  obtain ⟨i, hi⟩ := hσ
  obtain ⟨j, hj⟩ := hUV i
  exact ⟨j, hi.trans hj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices_le ``Submission.DifferentialGeometry.Homology.smallSingularSimplices_le


theorem smallSingularSimplices_eq_top (hU : ∃ i, U i = Set.univ) :
    smallSingularSimplices X U = ⊤ := by
  obtain ⟨i, hi⟩ := hU
  apply top_unique
  intro n σ _
  exact ⟨i, hi ▸ Set.subset_univ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices_eq_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices_eq_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices_eq_top ``Submission.DifferentialGeometry.Homology.smallSingularSimplices_eq_top


theorem smallSingularSimplices_obj_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    (smallSingularSimplices X U).obj (_root_.Opposite.op ⦋0⦌) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro σ
  obtain ⟨i, hi⟩ := hU (X.toSSetObjEquiv _ σ _root_.Inhabited.default)
  refine ⟨i, ?_⟩
  rintro _ ⟨z, rfl⟩
  simpa only [Subsingleton.elim z _root_.Inhabited.default] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplices_obj_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplices_obj_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplices_obj_zero ``Submission.DifferentialGeometry.Homology.smallSingularSimplices_obj_zero

variable {X U} {Y : TopCat.{u}} {κ : Type w} {V : κ → Set Y}


def smallSingularSimplicesMap (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    (smallSingularSimplices X U : SSet) ⟶ smallSingularSimplices Y V where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map f).app n σ.val, by
    obtain ⟨i, hi⟩ := σ.property
    obtain ⟨j, hj⟩ := hf i
    refine ⟨j, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hj (hi ⟨z, rfl⟩)⟩
  naturality _ _ _ := by
    ext σ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((TopCat.toSSet.map f).naturality _) σ.val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplicesMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplicesMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplicesMap ``Submission.DifferentialGeometry.Homology.smallSingularSimplicesMap


@[reassoc (attr := simp)]
theorem smallSingularSimplicesMap_ι (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    smallSingularSimplicesMap f hf ≫ (smallSingularSimplices Y V).ι =
      (smallSingularSimplices X U).ι ≫ TopCat.toSSet.map f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallSingularSimplicesMap_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallSingularSimplicesMap_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallSingularSimplicesMap_ι ``Submission.DifferentialGeometry.Homology.smallSingularSimplicesMap_ι

variable (X U) {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def smallChainMap :
    (smallSingularSimplices X U : SSet).chainComplex R ⟶
      ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X :=
  SSet.chainComplexMap (smallSingularSimplices X U).ι R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainMap ``Submission.DifferentialGeometry.Homology.smallChainMap


@[reassoc (attr := simp)]
theorem ι_smallChainMap_f {n : ℕ}
    (σ : (smallSingularSimplices X U : SSet) _⦋n⦌) :
    (smallSingularSimplices X U : SSet).ιChainComplex σ ≫ (smallChainMap X U R).f n =
      (TopCat.toSSet.obj X).ιChainComplex σ.val :=
  SSet.ι_chainComplexMap_f _ _ _ R σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.ι_smallChainMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.ι_smallChainMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.ι_smallChainMap_f ``Submission.DifferentialGeometry.Homology.ι_smallChainMap_f

private def smallChainProjection (n : ℕ) :
    (((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).obj X).X n ⟶
      ((smallSingularSimplices X U : SSet).chainComplex R).X n := by
  classical
  exact Sigma.desc (fun σ ↦ if hσ : σ ∈ (smallSingularSimplices X U).obj (_root_.Opposite.op ⦋n⦌)
    then (smallSingularSimplices X U : SSet).ιChainComplex ⟨σ, hσ⟩ else 0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.smallChainProjection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.smallChainProjection target :: scope.openDecls } }

private theorem smallChainMap_projection (n : ℕ) :
    (smallChainMap X U R).f n ≫ smallChainProjection X U R n = 𝟙 _ := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, ι_smallChainMap_f]
  change Sigma.ι _ σ.val ≫ Sigma.desc _ = _
  rw [Sigma.ι_desc]
  simp only [dif_pos σ.property, Category.comp_id]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.smallChainMap_projection
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.smallChainMap_projection target :: scope.openDecls } }


theorem mono_smallChainMap_f (n : ℕ) : _root_.CategoryTheory.Mono ((smallChainMap X U R).f n) := by
  have : _root_.CategoryTheory.IsSplitMono ((smallChainMap X U R).f n) :=
    IsSplitMono.mk' ⟨smallChainProjection X U R n, smallChainMap_projection X U R n⟩
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.mono_smallChainMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.mono_smallChainMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.mono_smallChainMap_f ``Submission.DifferentialGeometry.Homology.mono_smallChainMap_f


theorem mono_smallChainMap : _root_.CategoryTheory.Mono (smallChainMap X U R) :=
  HomologicalComplex.mono_of_mono_f _ (mono_smallChainMap_f X U R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.mono_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.mono_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.mono_smallChainMap ``Submission.DifferentialGeometry.Homology.mono_smallChainMap


theorem isIso_smallChainMap_f_zero (hU : ∀ x : X, ∃ i, x ∈ U i) :
    IsIso ((smallChainMap X U R).f 0) := by
  refine ⟨⟨smallChainProjection X U R 0, smallChainMap_projection X U R 0, ?_⟩⟩
  apply SSet.chainComplex_hom_ext
  intro σ
  have hσ : σ ∈ (smallSingularSimplices X U).obj (_root_.Opposite.op ⦋0⦌) := by
    rw [smallSingularSimplices_obj_zero X U hU]
    exact Set.mem_univ _
  change Sigma.ι _ σ ≫ (Sigma.desc _ ≫ _) = _
  rw [← Category.assoc, Sigma.ι_desc]
  simp only [dif_pos hσ]
  exact (ι_smallChainMap_f X U R ⟨σ, hσ⟩).trans (Category.comp_id _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.isIso_smallChainMap_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.isIso_smallChainMap_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.isIso_smallChainMap_f_zero ``Submission.DifferentialGeometry.Homology.isIso_smallChainMap_f_zero


theorem smallChainMap_naturality (f : X ⟶ Y)
    (hf : ∀ i, ∃ j, Set.MapsTo f (U i) (V j)) :
    SSet.chainComplexMap (smallSingularSimplicesMap f hf) R ≫ smallChainMap Y V R =
      smallChainMap X U R ≫
        ((_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).obj R).map f := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smallSingularSimplicesMap_ι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainMap_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainMap_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainMap_naturality ``Submission.DifferentialGeometry.Homology.smallChainMap_naturality


def smallChainRefinement {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    (smallSingularSimplices X U : SSet).chainComplex R ⟶
      (smallSingularSimplices X V : SSet).chainComplex R :=
  SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (smallSingularSimplices_le X U V hUV)) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainRefinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainRefinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainRefinement ``Submission.DifferentialGeometry.Homology.smallChainRefinement


@[reassoc (attr := simp)]
theorem smallChainRefinement_smallChainMap {κ : Type w} (V : κ → Set X)
    (hUV : ∀ i, ∃ j, U i ⊆ V j) :
    smallChainRefinement X U R V hUV ≫ smallChainMap X V R = smallChainMap X U R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ = _
  rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.smallChainRefinement_smallChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.smallChainRefinement_smallChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.smallChainRefinement_smallChainMap ``Submission.DifferentialGeometry.Homology.smallChainRefinement_smallChainMap

end DifferentialGeometry.Homology
