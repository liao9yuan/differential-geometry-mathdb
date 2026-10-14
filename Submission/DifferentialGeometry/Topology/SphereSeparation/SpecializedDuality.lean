import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Submission.DifferentialGeometry.Topology.SphereSeparation.AlexanderDuality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Simplicial
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Simplicial

namespace DifferentialGeometry.Topology.SphereSeparation



noncomputable abbrev integerSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainComplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChainComplex


noncomputable def integerSingularChainMap {X Y : TopCat} (f : X ⟶ Y) :
    integerSingularChainComplex X ⟶ integerSingularChainComplex Y :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap

@[simp]
theorem integerSingularChainMap_id (X : TopCat) :
    integerSingularChainMap (𝟙 X) = 𝟙 (integerSingularChainComplex X) :=
  by simp [integerSingularChainMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_id ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_id

@[simp]
theorem integerSingularChainMap_comp {X Y Z : TopCat}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    integerSingularChainMap (f ≫ g) =
      integerSingularChainMap f ≫ integerSingularChainMap g :=
  Functor.map_comp _ f g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp

noncomputable abbrev relativeSingularChainComplex {A X : TopCat} (i : A ⟶ X) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  _root_.CategoryTheory.Limits.cokernel (integerSingularChainMap i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainComplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainComplex

noncomputable abbrev relativeSingularHomology {A X : TopCat} (i : A ⟶ X)
    (n : ℕ) : ModuleCat ℤ :=
  (relativeSingularChainComplex i).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology


noncomputable abbrev relativeSingularChainProjection {A X : TopCat} (i : A ⟶ X) :
    integerSingularChainComplex X ⟶ relativeSingularChainComplex i :=
  cokernel.π (integerSingularChainMap i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection

@[reassoc]
theorem integerSingularChainMap_comp_relativeProjection
    {A X : TopCat} (i : A ⟶ X) :
    integerSingularChainMap i ≫ relativeSingularChainProjection i = 0 :=
  cokernel.condition (integerSingularChainMap i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp_relativeProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp_relativeProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp_relativeProjection ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularChainMap_comp_relativeProjection

noncomputable def relativeSingularChainMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    relativeSingularChainComplex i ⟶ relativeSingularChainComplex j :=
  cokernel.map
    (integerSingularChainMap i) (integerSingularChainMap j)
    (integerSingularChainMap fA) (integerSingularChainMap fX) (by
      rw [← integerSingularChainMap_comp, h, integerSingularChainMap_comp])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap

@[reassoc (attr := simp)]
theorem relativeSingularChainProjection_naturality
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    relativeSingularChainProjection i ≫
        relativeSingularChainMap i j fA fX h =
      integerSingularChainMap fX ≫ relativeSingularChainProjection j := by
  simp [relativeSingularChainMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainProjection_naturality

@[simp]
theorem relativeSingularChainMap_id {A X : TopCat} (i : A ⟶ X) :
    relativeSingularChainMap i i (𝟙 A) (𝟙 X) (by simp) =
      𝟙 (relativeSingularChainComplex i) := by
  simp [relativeSingularChainMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_id ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_id


theorem relativeSingularChainMap_comp
    {A X B Y C Z : TopCat}
    (i : A ⟶ X) (j : B ⟶ Y) (k : C ⟶ Z)
    (fA : A ⟶ B) (fX : X ⟶ Y) (hf : i ≫ fX = fA ≫ j)
    (gA : B ⟶ C) (gX : Y ⟶ Z) (hg : j ≫ gX = gA ≫ k) :
    relativeSingularChainMap i j fA fX hf ≫
        relativeSingularChainMap j k gA gX hg =
      relativeSingularChainMap i k (fA ≫ gA) (fX ≫ gX) (by
        rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]) := by
  apply (_root_.CategoryTheory.cancel_epi (relativeSingularChainProjection i)).1
  simp [Category.assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_comp ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMap_comp

theorem isIso_relativeSingularChainMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [_root_.CategoryTheory.IsIso fA] [_root_.CategoryTheory.IsIso fX] :
    IsIso (relativeSingularChainMap i j fA fX h) := by
  have h_inv : j ≫ _root_.CategoryTheory.inv fX = _root_.CategoryTheory.inv fA ≫ i := by
    apply (_root_.CategoryTheory.cancel_mono fX).1
    simp [Category.assoc, h]
  refine ⟨⟨relativeSingularChainMap j i (_root_.CategoryTheory.inv fA) (_root_.CategoryTheory.inv fX) h_inv, ?_, ?_⟩⟩
  · rw [relativeSingularChainMap_comp]
    simp
  · rw [relativeSingularChainMap_comp]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularChainMap

theorem isIso_relativeSingularHomologyMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [_root_.CategoryTheory.IsIso fA] [_root_.CategoryTheory.IsIso fX] (n : ℕ) :
    _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (relativeSingularChainMap i j fA fX h) n) := by
  let _ : _root_.CategoryTheory.IsIso (relativeSingularChainMap i j fA fX h) :=
    isIso_relativeSingularChainMap i j fA fX h
  exact (HomologicalComplex.homologyMapIso
    (_root_.CategoryTheory.asIso (relativeSingularChainMap i j fA fX h)) n).isIso_hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMap


def topologicalSubspaceInclusion
    {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceInclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceInclusion


noncomputable abbrev relativeSingularHomologyOfSubspace
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) : ModuleCat ℤ :=
  relativeSingularHomology (topologicalSubspaceInclusion A) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyOfSubspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyOfSubspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyOfSubspace ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyOfSubspace

def topologicalSubspaceMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨f x, h x x.2⟩,
      continuous_induced_rng.2 (f.continuous.comp continuous_subtype_val)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap

@[reassoc]
theorem topologicalSubspaceMap_comm
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) :
    topologicalSubspaceInclusion A ≫ TopCat.ofHom f =
      topologicalSubspaceMap f A B h ≫ topologicalSubspaceInclusion B := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap_comm ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSubspaceMap_comm

noncomputable def relativeSingularChainMapOfSubspaces
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) :
    relativeSingularChainComplex (topologicalSubspaceInclusion A) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion B) :=
  relativeSingularChainMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMapOfSubspaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMapOfSubspaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMapOfSubspaces ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainMapOfSubspaces


noncomputable def relativeSingularHomologyMapOfSubspaces
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    relativeSingularHomologyOfSubspace A n ⟶
      relativeSingularHomologyOfSubspace B n :=
  HomologicalComplex.homologyMap
    (relativeSingularChainMapOfSubspaces f A B h) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyMapOfSubspaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyMapOfSubspaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyMapOfSubspaces ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomologyMapOfSubspaces

theorem isIso_relativeSingularHomologyMapOfSubspaces
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B)
    (hf : IsHomeomorph f)
    (hsub : IsHomeomorph (topologicalSubspaceMap f A B h))
    (n : ℕ) : _root_.CategoryTheory.IsIso (relativeSingularHomologyMapOfSubspaces f A B h n) := by
  let _ : _root_.CategoryTheory.IsIso (TopCat.ofHom f) :=
    (TopCat.isIso_iff_isHomeomorph (TopCat.ofHom f)).2 hf
  let _ : _root_.CategoryTheory.IsIso (topologicalSubspaceMap f A B h) :=
    (TopCat.isIso_iff_isHomeomorph (topologicalSubspaceMap f A B h)).2 hsub
  exact isIso_relativeSingularHomologyMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces


def subspaceOutside
    {X : Type} (A U : Set X) : Set (Uᶜ : Set X) :=
  {x | x.1 ∈ A}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceOutside then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceOutside"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceOutside ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceOutside

def subspaceOutsideHomeomorphDiff
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    subspaceOutside A U ≃ₜ (A \ U : Set X) where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphDiff ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideHomeomorphDiff

noncomputable def excisionRelativeSingularChainMap
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion A) :=
    relativeSingularChainMapOfSubspaces
    ⟨(Subtype.val : (Uᶜ : Set X) → X), continuous_subtype_val⟩
    (subspaceOutside A U) A (fun _ hx ↦ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularChainMap


noncomputable def excisionRelativeSingularHomologyMap
    {X : Type} [TopologicalSpace X] (A U : Set X) (n : ℕ) :
    relativeSingularHomologyOfSubspace (subspaceOutside A U) n ⟶
      relativeSingularHomologyOfSubspace A n :=
  HomologicalComplex.homologyMap (excisionRelativeSingularChainMap A U) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularHomologyMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionRelativeSingularHomologyMap

def SingularExcisionFor
    {X : Type} [TopologicalSpace X] (A U : Set X) : Prop :=
  closure U ⊆ interior A →
    ∀ n : ℕ, _root_.CategoryTheory.IsIso (excisionRelativeSingularHomologyMap A U n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SingularExcisionFor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SingularExcisionFor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SingularExcisionFor ``Submission.DifferentialGeometry.Topology.SphereSeparation.SingularExcisionFor

def excisionCoverNear
    {X : Type} [TopologicalSpace X] (A : Set X) : Set X :=
  interior A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear

def excisionCoverFar
    {X : Type} [TopologicalSpace X] (U : Set X) : Set X :=
  (closure U)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar

theorem isOpen_excisionCoverNear
    {X : Type} [TopologicalSpace X] (A : Set X) :
    IsOpen (excisionCoverNear A) :=
  isOpen_interior

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverNear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverNear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverNear ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverNear

theorem isOpen_excisionCoverFar
    {X : Type} [TopologicalSpace X] (U : Set X) :
    IsOpen (excisionCoverFar U) :=
  isClosed_closure.isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverFar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverFar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverFar ``Submission.DifferentialGeometry.Topology.SphereSeparation.isOpen_excisionCoverFar

theorem excisionCoverNear_subset
    {X : Type} [TopologicalSpace X] (A : Set X) :
    excisionCoverNear A ⊆ A :=
  interior_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear_subset ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionCoverNear_subset

theorem excisionCoverFar_subset
    {X : Type} [TopologicalSpace X] (U : Set X) :
    excisionCoverFar U ⊆ Uᶜ :=
  Set.compl_subset_compl.mpr subset_closure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar_subset ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionCoverFar_subset

theorem excisionCover_union
    {X : Type} [TopologicalSpace X] {A U : Set X}
    (h : closure U ⊆ interior A) :
    excisionCoverNear A ∪ excisionCoverFar U = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ closure U
  · exact Or.inl (h hx)
  · exact Or.inr hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.excisionCover_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.excisionCover_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.excisionCover_union ``Submission.DifferentialGeometry.Topology.SphereSeparation.excisionCover_union

abbrev TopologicalSingularSimplex
    (X : Type) [TopologicalSpace X] (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.TopologicalSingularSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.TopologicalSingularSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.TopologicalSingularSimplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.TopologicalSingularSimplex

def SingularSimplexSmallFor
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (V W : Set X) (s : TopologicalSingularSimplex X n) : Prop :=
  Set.range s ⊆ V ∨ Set.range s ⊆ W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SingularSimplexSmallFor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SingularSimplexSmallFor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SingularSimplexSmallFor ``Submission.DifferentialGeometry.Topology.SphereSeparation.SingularSimplexSmallFor

theorem singularZeroSimplex_smallFor_twoSetCover
    {X : Type} [TopologicalSpace X] {V W : Set X}
    (hcover : V ∪ W = Set.univ)
    (s : TopologicalSingularSimplex X 0) :
    SingularSimplexSmallFor V W s := by
  have hx : s _root_.Inhabited.default ∈ V ∪ W := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hx with hx | hx
  · left
    rintro y ⟨z, rfl⟩
    simpa only [Subsingleton.elim z _root_.Inhabited.default] using hx
  · right
    rintro y ⟨z, rfl⟩
    simpa only [Subsingleton.elim z _root_.Inhabited.default] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_twoSetCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_twoSetCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_twoSetCover ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_twoSetCover

theorem singularZeroSimplex_smallFor_excisionCover
    {X : Type} [TopologicalSpace X] {A U : Set X}
    (h : closure U ⊆ interior A)
    (s : TopologicalSingularSimplex X 0) :
    SingularSimplexSmallFor (excisionCoverNear A) (excisionCoverFar U) s :=
  singularZeroSimplex_smallFor_twoSetCover (excisionCover_union h) s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_excisionCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_excisionCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_excisionCover ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularZeroSimplex_smallFor_excisionCover


def singularSimplexExcisionPullbackCover
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (A U : Set X) (s : TopologicalSingularSimplex X n) :
    Set (Set (stdSimplex ℝ (Fin (n + 1)))) :=
  {s ⁻¹' excisionCoverNear A, s ⁻¹' excisionCoverFar U}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularSimplexExcisionPullbackCover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularSimplexExcisionPullbackCover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularSimplexExcisionPullbackCover ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularSimplexExcisionPullbackCover

theorem singularSimplex_excisionLebesgueNumber
    {X : Type} [TopologicalSpace X] {n : ℕ} {A U : Set X}
    (h : closure U ⊆ interior A)
    (s : TopologicalSingularSimplex X n) :
    ∃ δ > 0, ∀ x : stdSimplex ℝ (Fin (n + 1)),
      ∃ V ∈ singularSimplexExcisionPullbackCover A U s,
        Metric.ball x δ ⊆ V := by
  have hopen : ∀ V ∈ singularSimplexExcisionPullbackCover A U s, IsOpen V := by
    intro V hV
    rcases hV with (rfl | rfl)
    · exact (isOpen_excisionCoverNear A).preimage s.continuous
    · exact (isOpen_excisionCoverFar U).preimage s.continuous
  have hcover : Set.univ ⊆ ⋃₀ singularSimplexExcisionPullbackCover A U s := by
    intro x _
    have hx : s x ∈ excisionCoverNear A ∪ excisionCoverFar U := by
      rw [excisionCover_union h]
      exact Set.mem_univ _
    rcases hx with hx | hx
    · exact Set.mem_sUnion_of_mem
        (t := s ⁻¹' excisionCoverNear A) hx
        (by simp [singularSimplexExcisionPullbackCover])
    · exact Set.mem_sUnion_of_mem
        (t := s ⁻¹' excisionCoverFar U) hx
        (by simp [singularSimplexExcisionPullbackCover])
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric_sUnion isCompact_univ hopen hcover
  exact ⟨δ, hδ, fun x ↦ hball x (Set.mem_univ x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularSimplex_excisionLebesgueNumber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularSimplex_excisionLebesgueNumber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularSimplex_excisionLebesgueNumber ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularSimplex_excisionLebesgueNumber

def topologicalSingularSimplexLift
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : TopologicalSingularSimplex X n) (A : Set X)
    (h : Set.range s ⊆ A) : TopologicalSingularSimplex A n :=
  ⟨fun x ↦ ⟨s x, h ⟨x, rfl⟩⟩, by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift

@[simp]
theorem topologicalSingularSimplexLift_coe
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (s : TopologicalSingularSimplex X n) (A : Set X)
    (h : Set.range s ⊆ A)
    (x : stdSimplex ℝ (Fin (n + 1))) :
    (topologicalSingularSimplexLift s A h x : X) = s x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift_coe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift_coe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift_coe ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSingularSimplexLift_coe

theorem singularSimplexSmallFor_excisionCover_factor
    {X : Type} [TopologicalSpace X] {n : ℕ} {A U : Set X}
    {s : TopologicalSingularSimplex X n}
    (hs : SingularSimplexSmallFor
      (excisionCoverNear A) (excisionCoverFar U) s) :
    (∃ t : TopologicalSingularSimplex A n,
        ∀ x, (t x : X) = s x) ∨
      (∃ t : TopologicalSingularSimplex (Uᶜ : Set X) n,
        ∀ x, (t x : X) = s x) := by
  rcases hs with hs | hs
  · left
    let hA : Set.range s ⊆ A :=
      hs.trans (excisionCoverNear_subset A)
    exact ⟨topologicalSingularSimplexLift s A hA, fun _ ↦ rfl⟩
  · right
    let hU : Set.range s ⊆ Uᶜ :=
      hs.trans (excisionCoverFar_subset U)
    exact ⟨topologicalSingularSimplexLift s Uᶜ hU, fun _ ↦ rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularSimplexSmallFor_excisionCover_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularSimplexSmallFor_excisionCover_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularSimplexSmallFor_excisionCover_factor ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularSimplexSmallFor_excisionCover_factor



noncomputable def smallSingularSubcomplex
    (X : TopCat) (V W : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubspaceInclusion V)) ⊔
    SSet.Subcomplex.range
      (TopCat.toSSet.map (topologicalSubspaceInclusion W))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex

@[simp]
theorem toSSetObjZeroEquiv_map
    {X Y : TopCat} (f : X ⟶ Y)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk 0))) :
    TopCat.toSSetObj₀Equiv
        ((TopCat.toSSet.map f).app _ x) =
      f (TopCat.toSSetObj₀Equiv x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.toSSetObjZeroEquiv_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.toSSetObjZeroEquiv_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.toSSetObjZeroEquiv_map ``Submission.DifferentialGeometry.Topology.SphereSeparation.toSSetObjZeroEquiv_map

theorem smallSingularSubcomplex_obj_zero_eq_univ
    (X : TopCat) (V W : Set X) (hcover : V ∪ W = Set.univ) :
    (smallSingularSubcomplex X V W).obj
      (Opposite.op (SimplexCategory.mk 0)) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have hx : TopCat.toSSetObj₀Equiv x ∈ V ∪ W := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hx with hx | hx
  · apply Or.inl
    refine ⟨TopCat.toSSetObj₀Equiv.symm
      ⟨TopCat.toSSetObj₀Equiv x, hx⟩, ?_⟩
    apply TopCat.toSSetObj₀Equiv.injective
    simp [topologicalSubspaceInclusion]
  · apply Or.inr
    refine ⟨TopCat.toSSetObj₀Equiv.symm
      ⟨TopCat.toSSetObj₀Equiv x, hx⟩, ?_⟩
    apply TopCat.toSSetObj₀Equiv.injective
    simp [topologicalSubspaceInclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex_obj_zero_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex_obj_zero_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex_obj_zero_eq_univ ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallSingularSubcomplex_obj_zero_eq_univ

theorem isIso_smallSingularSubcomplex_inclusion_app_zero
    (X : TopCat) (V W : Set X) (hcover : V ∪ W = Set.univ) :
    _root_.CategoryTheory.IsIso ((smallSingularSubcomplex X V W).ι.app
      (Opposite.op (SimplexCategory.mk 0))) := by
  apply (_root_.CategoryTheory.isIso_iff_bijective _).2
  constructor
  · exact Subtype.val_injective
  · intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [smallSingularSubcomplex_obj_zero_eq_univ X V W hcover]
    exact Set.mem_univ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularSubcomplex_inclusion_app_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularSubcomplex_inclusion_app_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularSubcomplex_inclusion_app_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularSubcomplex_inclusion_app_zero


noncomputable abbrev smallSingularChainComplex
    (X : TopCat) (V W : Set X) : ChainComplex (ModuleCat ℤ) ℕ :=
  (smallSingularSubcomplex X V W : SSet).chainComplex
    (ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallSingularChainComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallSingularChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallSingularChainComplex ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallSingularChainComplex


noncomputable def smallSingularChainInclusion
    (X : TopCat) (V W : Set X) :
    smallSingularChainComplex X V W ⟶ integerSingularChainComplex X :=
  SSet.chainComplexMap (smallSingularSubcomplex X V W).ι
    (ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smallSingularChainInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smallSingularChainInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smallSingularChainInclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.smallSingularChainInclusion


theorem mono_smallSingularChainInclusion
    (X : TopCat) (V W : Set X) :
    Mono (smallSingularChainInclusion X V W) := by
  dsimp [smallSingularChainInclusion, integerSingularChainComplex,
    smallSingularChainComplex, AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexMap, SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, _root_.CategoryTheory.SimplicialObject]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_smallSingularChainInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_smallSingularChainInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_smallSingularChainInclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_smallSingularChainInclusion

theorem isIso_smallSingularChainInclusion_f_zero
    (X : TopCat) (V W : Set X) (hcover : V ∪ W = Set.univ) :
    IsIso ((smallSingularChainInclusion X V W).f 0) := by
  let i₀ := (smallSingularSubcomplex X V W).ι.app
    (Opposite.op (SimplexCategory.mk 0))
  let _ : _root_.CategoryTheory.IsIso i₀ :=
    isIso_smallSingularSubcomplex_inclusion_app_zero X V W hcover
  let e : (smallSingularSubcomplex X V W : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) ≃
      (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)) :=
    Equiv.ofBijective i₀ ((_root_.CategoryTheory.isIso_iff_bijective i₀).1 inferInstance)
  dsimp [smallSingularChainInclusion, integerSingularChainComplex,
    smallSingularChainComplex, AlgebraicTopology.singularChainComplexFunctor,
    SSet.chainComplexMap, SSet.chainComplexFunctor,
    AlgebraicTopology.alternatingFaceMapComplex,
    SimplicialObject.whiskering, _root_.CategoryTheory.SimplicialObject]
  change _root_.CategoryTheory.IsIso (Sigma.map'
    (f := fun _ : (smallSingularSubcomplex X V W : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
    (g := fun _ : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
    (fun x : (smallSingularSubcomplex X V W : SSet).obj
        (Opposite.op (SimplexCategory.mk 0)) ↦
      (x : (TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk 0))))
    (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)))
  simpa [e, i₀] using
    (Sigma.whiskerEquiv
      (C := ModuleCat ℤ)
      (f := fun _ : (smallSingularSubcomplex X V W : SSet).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
      (g := fun _ : (TopCat.toSSet.obj X).obj
          (Opposite.op (SimplexCategory.mk 0)) ↦ ModuleCat.of ℤ ℤ)
      e (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))).isIso_hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularChainInclusion_f_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularChainInclusion_f_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularChainInclusion_f_zero ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_smallSingularChainInclusion_f_zero

def SmallChainsSubdivisionFor
    (X : TopCat) (V W : Set X) : Prop :=
  IsOpen V ∧ IsOpen W ∧ V ∪ W = Set.univ ∧
    ∀ n : ℕ, _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (smallSingularChainInclusion X V W) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SmallChainsSubdivisionFor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SmallChainsSubdivisionFor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SmallChainsSubdivisionFor ``Submission.DifferentialGeometry.Topology.SphereSeparation.SmallChainsSubdivisionFor

def complEmptyHomeomorph
    (X : Type) [TopologicalSpace X] :
    ((∅ : Set X)ᶜ : Set X) ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.complEmptyHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.complEmptyHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.complEmptyHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.complEmptyHomeomorph

def subspaceOutsideEmptyHomeomorph
    {X : Type} [TopologicalSpace X] (A : Set X) :
    subspaceOutside A (∅ : Set X) ≃ₜ A where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, by simp⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideEmptyHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideEmptyHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideEmptyHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceOutsideEmptyHomeomorph

theorem isIso_excisionRelativeSingularHomologyMap_empty
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    IsIso (excisionRelativeSingularHomologyMap A (∅ : Set X) n) := by
  change _root_.CategoryTheory.IsIso (relativeSingularHomologyMapOfSubspaces
    ⟨(Subtype.val : ((∅ : Set X)ᶜ : Set X) → X), continuous_subtype_val⟩
    (subspaceOutside A (∅ : Set X)) A (fun _ hx ↦ hx) n)
  apply isIso_relativeSingularHomologyMapOfSubspaces
  · exact (complEmptyHomeomorph X).isHomeomorph
  · exact (subspaceOutsideEmptyHomeomorph A).isHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_excisionRelativeSingularHomologyMap_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_excisionRelativeSingularHomologyMap_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_excisionRelativeSingularHomologyMap_empty ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_excisionRelativeSingularHomologyMap_empty

theorem mono_integerSingularChainMap_subspace
    {X : Type} [TopologicalSpace X] (A : Set X) :
    Mono (integerSingularChainMap (topologicalSubspaceInclusion A)) := by
  let i := topologicalSubspaceInclusion A
  let _ : _root_.CategoryTheory.Mono i := (TopCat.mono_iff_injective i).2 Subtype.val_injective
  change _root_.CategoryTheory.Mono
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map i)
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.mono_integerSingularChainMap_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.mono_integerSingularChainMap_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.mono_integerSingularChainMap_subspace ``Submission.DifferentialGeometry.Topology.SphereSeparation.mono_integerSingularChainMap_subspace


noncomputable abbrev relativeSingularChainSequenceOfMap
    {A X : TopCat} (i : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (integerSingularChainMap i)
    (relativeSingularChainProjection i)
    (integerSingularChainMap_comp_relativeProjection i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceOfMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceOfMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceOfMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceOfMap


noncomputable abbrev relativeSingularChainSequence
    {X : Type} [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  relativeSingularChainSequenceOfMap (topologicalSubspaceInclusion A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence

theorem relativeSingularChainSequence_shortExact
    {X : Type} [TopologicalSpace X] (A : Set X) :
    (relativeSingularChainSequence A).ShortExact := by
  change (ShortComplex.cokernelSequence
    (integerSingularChainMap (topologicalSubspaceInclusion A))).ShortExact
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.cokernelSequence_exact
      (integerSingularChainMap (topologicalSubspaceInclusion A))
  · exact mono_integerSingularChainMap_subspace A
  · infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence_shortExact ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequence_shortExact

noncomputable def relativeSingularChainSequenceMap
    {A X B Y : TopCat} (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    relativeSingularChainSequenceOfMap i ⟶
      relativeSingularChainSequenceOfMap j where
  τ₁ := integerSingularChainMap fA
  τ₂ := integerSingularChainMap fX
  τ₃ := relativeSingularChainMap i j fA fX h
  comm₁₂ := by
    change integerSingularChainMap fA ≫ integerSingularChainMap j =
      integerSingularChainMap i ≫ integerSingularChainMap fX
    rw [← integerSingularChainMap_comp, ← integerSingularChainMap_comp, h]
  comm₂₃ := by
    exact (relativeSingularChainProjection_naturality i j fA fX h).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularChainSequenceMap


noncomputable abbrev cokernelChainSequence
    {A X : ChainComplex (ModuleCat ℤ) ℕ} (i : A ⟶ X) :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk i (cokernel.π i) (cokernel.condition i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequence ``Submission.DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequence

noncomputable def cokernelChainSequenceMap
    {A X B Y : ChainComplex (ModuleCat ℤ) ℕ}
    (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j) :
    cokernelChainSequence i ⟶ cokernelChainSequence j where
  τ₁ := fA
  τ₂ := fX
  τ₃ := cokernel.map i j fA fX h
  comm₁₂ := h.symm
  comm₂₃ := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequenceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequenceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequenceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.cokernelChainSequenceMap

theorem quasiIso_cokernelMap
    {A X B Y : ChainComplex (ModuleCat ℤ) ℕ}
    (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [_root_.CategoryTheory.Mono i] [_root_.CategoryTheory.Mono j] (hA : QuasiIso fA) (hX : QuasiIso fX) :
    QuasiIso (cokernel.map i j fA fX h) := by
  have hi : (cokernelChainSequence i).ShortExact := by
    change (ShortComplex.cokernelSequence i).ShortExact
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.cokernelSequence_exact i
    · change _root_.CategoryTheory.Mono i
      infer_instance
    · infer_instance
  have hj : (cokernelChainSequence j).ShortExact := by
    change (ShortComplex.cokernelSequence j).ShortExact
    apply ShortComplex.ShortExact.mk'
    · exact ShortComplex.cokernelSequence_exact j
    · change _root_.CategoryTheory.Mono j
      infer_instance
    · infer_instance
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (cokernelChainSequenceMap i j fA fX h) hi hj hA hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_cokernelMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_cokernelMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_cokernelMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_cokernelMap


theorem isIso_homologyMap_cokernelMap
    {A X B Y : ChainComplex (ModuleCat ℤ) ℕ}
    (i : A ⟶ X) (j : B ⟶ Y)
    (fA : A ⟶ B) (fX : X ⟶ Y) (h : i ≫ fX = fA ≫ j)
    [_root_.CategoryTheory.Mono i] [_root_.CategoryTheory.Mono j] (hA : QuasiIso fA) (hX : QuasiIso fX)
    (n : ℕ) :
    _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (cokernel.map i j fA fX h) n) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  let _ : QuasiIso (cokernel.map i j fA fX h) :=
    quasiIso_cokernelMap i j fA fX h hA hX
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_homologyMap_cokernelMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_homologyMap_cokernelMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_homologyMap_cokernelMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_homologyMap_cokernelMap

theorem quasiIso_relativeSingularChainMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B)
    (hA : QuasiIso
      (integerSingularChainMap (topologicalSubspaceMap f A B h)))
    (hX : QuasiIso
      (integerSingularChainMap (TopCat.ofHom f))) :
    QuasiIso
      (relativeSingularChainMapOfSubspaces f A B h) := by
  let φ := relativeSingularChainSequenceMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (relativeSingularChainSequence_shortExact A)
    (relativeSingularChainSequence_shortExact B) hA hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.quasiIso_relativeSingularChainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.quasiIso_relativeSingularChainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.quasiIso_relativeSingularChainMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.quasiIso_relativeSingularChainMap


theorem isIso_relativeSingularHomologyMapOfSubspaces_of_quasiIso
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B)
    (hA : QuasiIso
      (integerSingularChainMap (topologicalSubspaceMap f A B h)))
    (hX : QuasiIso
      (integerSingularChainMap (TopCat.ofHom f)))
    (n : ℕ) :
    IsIso (relativeSingularHomologyMapOfSubspaces f A B h n) := by
  change _root_.CategoryTheory.IsIso (HomologicalComplex.homologyMap
    (relativeSingularChainMapOfSubspaces f A B h) n)
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  let _ : QuasiIso (relativeSingularChainMapOfSubspaces f A B h) :=
    quasiIso_relativeSingularChainMap f A B h hA hX
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces_of_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces_of_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces_of_quasiIso ``Submission.DifferentialGeometry.Topology.SphereSeparation.isIso_relativeSingularHomologyMapOfSubspaces_of_quasiIso

noncomputable abbrev integerSingularHomology (X : TopCat) (n : ℕ) :
    ModuleCat ℤ :=
  (integerSingularChainComplex X).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.integerSingularHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.integerSingularHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.integerSingularHomology ``Submission.DifferentialGeometry.Topology.SphereSeparation.integerSingularHomology


noncomputable def subspaceSingularHomologyMap
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    integerSingularHomology (TopCat.of A) n ⟶
      integerSingularHomology (TopCat.of X) n :=
  HomologicalComplex.homologyMap
    (integerSingularChainMap (topologicalSubspaceInclusion A)) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.subspaceSingularHomologyMap


noncomputable def absoluteToRelativeSingularHomology
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    integerSingularHomology (TopCat.of X) n ⟶
      relativeSingularHomologyOfSubspace A n :=
  HomologicalComplex.homologyMap
    (relativeSingularChainProjection (topologicalSubspaceInclusion A)) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.absoluteToRelativeSingularHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.absoluteToRelativeSingularHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.absoluteToRelativeSingularHomology ``Submission.DifferentialGeometry.Topology.SphereSeparation.absoluteToRelativeSingularHomology

noncomputable def relativeSingularBoundary
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    relativeSingularHomologyOfSubspace A (n + 1) ⟶
      integerSingularHomology (TopCat.of A) n :=
  (relativeSingularChainSequence_shortExact A).δ (n + 1) n (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary

theorem relativeSingularBoundary_naturality
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y)
    (h : ∀ x ∈ A, f x ∈ B) (n : ℕ) :
    relativeSingularHomologyMapOfSubspaces f A B h (n + 1) ≫
        relativeSingularBoundary B n =
      relativeSingularBoundary A n ≫
        HomologicalComplex.homologyMap
          (integerSingularChainMap (topologicalSubspaceMap f A B h)) n := by
  let φ := relativeSingularChainSequenceMap
    (topologicalSubspaceInclusion A) (topologicalSubspaceInclusion B)
    (topologicalSubspaceMap f A B h) (TopCat.ofHom f)
    (topologicalSubspaceMap_comm f A B h)
  exact (HomologicalComplex.HomologySequence.δ_naturality φ
    (relativeSingularChainSequence_shortExact A)
    (relativeSingularChainSequence_shortExact B) (n + 1) n (by simp)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary_naturality ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularBoundary_naturality


theorem relativeSingularHomology_exact_at_absolute
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (subspaceSingularHomologyMap A n)
      (absoluteToRelativeSingularHomology A n)
      (by
        dsimp [subspaceSingularHomologyMap,
          absoluteToRelativeSingularHomology,
          relativeSingularChainProjection]
        rw [← HomologicalComplex.homologyMap_comp]
        simp)).Exact := by
  simpa [relativeSingularChainSequence, ShortComplex.cokernelSequence,
    subspaceSingularHomologyMap,
    absoluteToRelativeSingularHomology, relativeSingularChainProjection,
    relativeSingularHomologyOfSubspace, relativeSingularHomology,
    relativeSingularChainComplex] using
    (relativeSingularChainSequence_shortExact A).homology_exact₂ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_absolute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_absolute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_absolute ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_absolute

theorem relativeSingularHomology_exact_at_relative
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (absoluteToRelativeSingularHomology A (n + 1))
      (relativeSingularBoundary A n)
      (by
        exact (relativeSingularChainSequence_shortExact A).comp_δ
          (n + 1) n (by simp))).Exact := by
  simpa [relativeSingularChainSequence, ShortComplex.cokernelSequence,
    absoluteToRelativeSingularHomology,
    relativeSingularBoundary, relativeSingularChainProjection,
    relativeSingularHomologyOfSubspace, relativeSingularHomology,
    relativeSingularChainComplex] using
    (relativeSingularChainSequence_shortExact A).homology_exact₃
      (n + 1) n (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_relative ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_relative


theorem relativeSingularHomology_exact_at_subspace
    {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ) :
    (ShortComplex.mk
      (relativeSingularBoundary A n)
      (subspaceSingularHomologyMap A n)
      (by
        exact (relativeSingularChainSequence_shortExact A).δ_comp
          (n + 1) n (by simp))).Exact := by
  simpa [relativeSingularChainSequence, ShortComplex.cokernelSequence,
    subspaceSingularHomologyMap,
    relativeSingularBoundary, relativeSingularHomologyOfSubspace,
    relativeSingularHomology, relativeSingularChainComplex] using
    (relativeSingularChainSequence_shortExact A).homology_exact₁
      (n + 1) n (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_subspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_subspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_subspace ``Submission.DifferentialGeometry.Topology.SphereSeparation.relativeSingularHomology_exact_at_subspace


def zerothHomotopyMapOfContinuousMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  ZerothHomotopy.lift (fun x ↦ ZerothHomotopy.mk (f x)) fun {_ _} p ↦
    ZerothHomotopy.sound (p.map f.continuous)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap

@[simp]
theorem zerothHomotopyMapOfContinuousMap_mk
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    zerothHomotopyMapOfContinuousMap f (ZerothHomotopy.mk x) =
      ZerothHomotopy.mk (f x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap_mk ``Submission.DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyMapOfContinuousMap_mk


noncomputable def zerothHomotopyEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) : ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := zerothHomotopyMapOfContinuousMap ⟨h, h.continuous⟩
  invFun := zerothHomotopyMapOfContinuousMap ⟨h.symm, h.symm.continuous⟩
  left_inv q := by
    induction q using ZerothHomotopy.rec with
    | mk x => simp
  right_inv q := by
    induction q using ZerothHomotopy.rec with
    | mk y => simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyEquivOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyEquivOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyEquivOfHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.zerothHomotopyEquivOfHomeomorph

noncomputable def reducedSingularH0IsoOfHomeomorph
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) :
    reducedSingularH0 (TopCat.of X) ≅ reducedSingularH0 (TopCat.of Y) :=
  reducedSingularH0IsoAugmentedFinsuppKernel (TopCat.of X) ≪≫
    (augmentationKernelCongr
      (zerothHomotopyEquivOfHomeomorph h)).toModuleIso ≪≫
    (reducedSingularH0IsoAugmentedFinsuppKernel (TopCat.of Y)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoOfHomeomorph ``Submission.DifferentialGeometry.Topology.SphereSeparation.reducedSingularH0IsoOfHomeomorph

noncomputable def euclideanComplementHomeomorphCompactifiedComplement
    (e : SphereTwo → EuclideanThree) :
    ((Set.range e)ᶜ : Set EuclideanThree) ≃ₜ
      ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree)) := by
  let f : ((Set.range e)ᶜ : Set EuclideanThree) → OnePoint EuclideanThree :=
    fun x ↦ (x.1 : OnePoint EuclideanThree)
  have hf : Topology.IsEmbedding f :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hrange :
      Set.range f =
        ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree)) := by
    rw [compl_alexanderDualityCompactum]
    ext y
    simp [f]
  exact hf.toHomeomorph.trans (Homeomorph.setCongr hrange)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.euclideanComplementHomeomorphCompactifiedComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.euclideanComplementHomeomorphCompactifiedComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.euclideanComplementHomeomorphCompactifiedComplement ``Submission.DifferentialGeometry.Topology.SphereSeparation.euclideanComplementHomeomorphCompactifiedComplement

noncomputable def euclideanComplementReducedH0IsoCompactifiedComplement
    (e : SphereTwo → EuclideanThree) :
    reducedSingularH0
        (TopCat.of ((Set.range e)ᶜ : Set EuclideanThree)) ≅
      reducedSingularH0
        (TopCat.of
          ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree))) :=
  reducedSingularH0IsoOfHomeomorph
    (euclideanComplementHomeomorphCompactifiedComplement e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.euclideanComplementReducedH0IsoCompactifiedComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.euclideanComplementReducedH0IsoCompactifiedComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.euclideanComplementReducedH0IsoCompactifiedComplement ``Submission.DifferentialGeometry.Topology.SphereSeparation.euclideanComplementReducedH0IsoCompactifiedComplement

def SpecializedAlexanderDuality
    (e : SphereTwo → EuclideanThree) : Prop :=
  Nonempty
    (reducedSingularH0
        (TopCat.of ((Set.range e)ᶜ : Set EuclideanThree)) ≅
      singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SpecializedAlexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SpecializedAlexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SpecializedAlexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.SpecializedAlexanderDuality

def CompactifiedSpecializedAlexanderDuality
    (e : SphereTwo → EuclideanThree) : Prop :=
  Nonempty
    (reducedSingularH0
        (TopCat.of
          ((alexanderDualityCompactum e)ᶜ : Set (OnePoint EuclideanThree))) ≅
      singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.CompactifiedSpecializedAlexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.CompactifiedSpecializedAlexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.CompactifiedSpecializedAlexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.CompactifiedSpecializedAlexanderDuality

theorem specializedAlexanderDuality_iff_compactified
    (e : SphereTwo → EuclideanThree) :
    SpecializedAlexanderDuality e ↔
      CompactifiedSpecializedAlexanderDuality e := by
  constructor
  · rintro ⟨h⟩
    exact ⟨
      (euclideanComplementReducedH0IsoCompactifiedComplement e).symm ≪≫ h⟩
  · rintro ⟨h⟩
    exact ⟨euclideanComplementReducedH0IsoCompactifiedComplement e ≪≫ h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_compactified then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_compactified"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_compactified ``Submission.DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_compactified

def SphereTwoSumPUnitH2IsInt : Prop :=
  Nonempty
    (singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
      ModuleCat.of ℤ ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereTwoSumPUnitH2IsInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereTwoSumPUnitH2IsInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereTwoSumPUnitH2IsInt ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereTwoSumPUnitH2IsInt

noncomputable def specializedAlexanderDualityIsoOfComponentCount
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcomponents :
      ConnectedComponents ((Set.range e)ᶜ : Set EuclideanThree) ≃ Fin 2)
    (hsphere :
      singularCohomology (TopCat.of (SphereTwo ⊕ PUnit)) 2 ≅
        ModuleCat.of ℤ ℤ) :
    reducedSingularH0
        (TopCat.of ((Set.range e)ᶜ : Set EuclideanThree)) ≅
      singularCohomology (TopCat.of (alexanderDualityCompactum e)) 2 := by
  let X := ((Set.range e)ᶜ : Set EuclideanThree)
  let _ : LocallyPathConnectedSpace X :=
    (isCompact_range he.contMDiff.continuous).isClosed.isOpen_compl.locallyPathConnectedSpace
  exact
    reducedSingularH0IsoIntOfZerothHomotopyEquiv (TopCat.of X)
        (connectedComponentsEquivZerothHomotopy.symm.trans hcomponents) ≪≫
      hsphere.symm ≪≫
      (alexanderDualityCompactumCohomologyIsoSphereTwoSumPUnit e he).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDualityIsoOfComponentCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDualityIsoOfComponentCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDualityIsoOfComponentCount ``Submission.DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDualityIsoOfComponentCount

theorem specializedAlexanderDuality_of_componentCount
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hcomponents : HasTwoComplementComponents e)
    (hsphere : SphereTwoSumPUnitH2IsInt) :
    SpecializedAlexanderDuality e := by
  obtain ⟨components⟩ := hcomponents
  obtain ⟨sphere⟩ := hsphere
  exact ⟨specializedAlexanderDualityIsoOfComponentCount e he components sphere⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_of_componentCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_of_componentCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_of_componentCount ``Submission.DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_of_componentCount

theorem hasAlexanderDualityH0Certificate_of_specializedDuality
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hduality : SpecializedAlexanderDuality e)
    (hsphere : SphereTwoSumPUnitH2IsInt) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_duality_and_sphereCohomology
    e he hduality hsphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_specializedDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_specializedDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_specializedDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasAlexanderDualityH0Certificate_of_specializedDuality

theorem specializedAlexanderDuality_iff_twoComponents
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (hsphere : SphereTwoSumPUnitH2IsInt) :
    SpecializedAlexanderDuality e ↔ HasTwoComplementComponents e := by
  constructor
  · intro hduality
    exact hasTwoComplementComponents_of_alexanderDualityH0Certificate e he
      (hasAlexanderDualityH0Certificate_of_specializedDuality e he hduality hsphere)
  · intro hcomponents
    exact specializedAlexanderDuality_of_componentCount e he hcomponents hsphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_twoComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_twoComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_twoComponents ``Submission.DifferentialGeometry.Topology.SphereSeparation.specializedAlexanderDuality_iff_twoComponents

end DifferentialGeometry.Topology.SphereSeparation
