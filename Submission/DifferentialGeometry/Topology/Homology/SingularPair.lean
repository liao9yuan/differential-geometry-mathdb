import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.QuasiIso
import Submission.DifferentialGeometry.MathlibCompat.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.AlgebraicTopology _root_.HomologicalComplex _root_.Submission.HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

abbrev integerCoefficients : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} ℤ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.integerCoefficients then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.integerCoefficients"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.integerCoefficients ``Submission.DifferentialGeometry.Topology.SingularPair.integerCoefficients

example : _root_.CategoryTheory.Abelian (ModuleCat.{u} ℤ) := inferInstance
example : HasCoproducts.{u} (ModuleCat.{u} ℤ) := inferInstance
example : _root_.CategoryTheory.CategoryWithHomology (ModuleCat.{u} ℤ) := inferInstance
instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instPreservesMonomorphismsTopCatSSetToSSet_differentialGeometry : TopCat.toSSet.{u}.PreservesMonomorphisms := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instPreservesMonomorphismsTopCatSSetToSSet_differentialGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instPreservesMonomorphismsTopCatSSetToSSet_differentialGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instPreservesMonomorphismsTopCatSSetToSSet_differentialGeometry ``Submission.DifferentialGeometry.Topology.SingularPair.instPreservesMonomorphismsTopCatSSetToSSet_differentialGeometry

variable (R : ModuleCat.{u} ℤ)

abbrev singularChainFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (_root_.AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularChainFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularChainFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularChainFunctor ``Submission.DifferentialGeometry.Topology.SingularPair.singularChainFunctor

abbrev singularChains (X : TopCat.{u}) : ChainComplex (ModuleCat.{u} ℤ) ℕ := (singularChainFunctor R).obj X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularChains then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularChains"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularChains ``Submission.DifferentialGeometry.Topology.SingularPair.singularChains

abbrev singularHomology (X : TopCat.{u}) (n : ℕ) : ModuleCat.{u} ℤ :=
  ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj R).obj X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomology ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomology

example (X : TopCat.{u}) (n : ℕ) : singularHomology R X n = (singularChains R X).homology n := rfl
example (X : TopCat.{u}) : singularChains R X = (TopCat.toSSet.obj X).chainComplex R := rfl

def incl (X : TopCat.{u}) (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.incl ``Submission.DifferentialGeometry.Topology.SingularPair.incl

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoTopCatIncl (X : TopCat.{u}) (A : Set X) : _root_.CategoryTheory.Mono (incl X A) :=
  (TopCat.mono_iff_injective _).2 Subtype.val_injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoTopCatIncl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoTopCatIncl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoTopCatIncl ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoTopCatIncl

abbrev singSub (X : TopCat.{u}) (A : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (incl X A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singSub ``Submission.DifferentialGeometry.Topology.SingularPair.singSub

lemma mem_singSub_iff (X : TopCat.{u}) (A : Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (singSub X A).obj n ↔ Set.range (X.toSSetObjEquiv n σ) ⊆ A := by
  constructor
  · rintro ⟨τ, rfl⟩ _ ⟨x, rfl⟩
    exact ((TopCat.of A).toSSetObjEquiv n τ x).2
  · intro h
    refine ⟨(TopCat.toSSetObjEquiv _ n).symm ⟨fun x => ⟨X.toSSetObjEquiv n σ x, h ⟨x, rfl⟩⟩,
      by fun_prop⟩, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext x
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mem_singSub_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mem_singSub_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mem_singSub_iff ``Submission.DifferentialGeometry.Topology.SingularPair.mem_singSub_iff

def pair (X : TopCat.{u}) (A : Set X) : SSetPair.{u} :=
  SSetPair.of (TopCat.toSSet.map (incl X A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pair then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pair"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pair ``Submission.DifferentialGeometry.Topology.SingularPair.pair

abbrev relativeHomology (X : TopCat.{u}) (A : Set X) (n : ℕ) : ModuleCat.{u} ℤ :=
  (pair X A).homology R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomology ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomology

example (X : TopCat.{u}) (A : Set X) (n : ℕ) : (pair X A).right.homology R n = singularHomology R X n := rfl
example (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (pair X A).left.homology R n = singularHomology R (TopCat.of A) n := rfl

abbrev inclMap (X : TopCat.{u}) (A : Set X) (n : ℕ) : singularHomology R (TopCat.of A) n ⟶ singularHomology R X n :=
  SSet.homologyMap (pair X A).hom R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclMap ``Submission.DifferentialGeometry.Topology.SingularPair.inclMap

example (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    inclMap R X A n = _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (incl X A)) n := rfl

abbrev relπ (X : TopCat.{u}) (A : Set X) (n : ℕ) : singularHomology R X n ⟶ relativeHomology R X A n :=
  (pair X A).homologyπ R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relπ ``Submission.DifferentialGeometry.Topology.SingularPair.relπ

abbrev δ (X : TopCat.{u}) (A : Set X) (n : ℕ) : relativeHomology R X A (n + 1) ⟶ singularHomology R (TopCat.of A) n :=
  (pair X A).homologyδ R (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ ``Submission.DifferentialGeometry.Topology.SingularPair.δ

theorem les_exact₁ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (δ R X A n) (inclMap R X A n)
      ((pair X A).homologyδ_comp R (n + 1) n rfl :)).Exact :=
  (pair X A).homology_exact₁ R (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.les_exact₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.les_exact₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.les_exact₁ ``Submission.DifferentialGeometry.Topology.SingularPair.les_exact₁

theorem les_exact₂ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (inclMap R X A n) (relπ R X A n)
      ((pair X A).homologyMap_hom_homologyπ R n :)).Exact :=
  (pair X A).homology_exact₂ R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.les_exact₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.les_exact₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.les_exact₂ ``Submission.DifferentialGeometry.Topology.SingularPair.les_exact₂

theorem les_exact₃ (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    (ShortComplex.mk (relπ R X A (n + 1)) (δ R X A n)
      ((pair X A).comp_homologyδ R (n + 1) n rfl :)).Exact :=
  (pair X A).homology_exact₃ R (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.les_exact₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.les_exact₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.les_exact₃ ``Submission.DifferentialGeometry.Topology.SingularPair.les_exact₃

def pairMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    pair X A ⟶ pair Y B :=
  SSetPair.homMk (TopCat.toSSet.map (TopCat.ofHom ⟨hf.restrict, by fun_prop⟩))
    (TopCat.toSSet.map f)
    (by
      change TopCat.toSSet.map _ ≫ TopCat.toSSet.map (incl Y B) =
        TopCat.toSSet.map (incl X A) ≫ TopCat.toSSet.map f
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap

abbrev relativeHomologyMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (n : ℕ) : relativeHomology R X A n ⟶ relativeHomology R Y B n :=
  SSetPair.homologyMap (pairMap f hf) R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap

def chainHomotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : HomotopyEquiv (singularChains R (TopCat.of X)) (singularChains R (TopCat.of Y)) where
  hom := (singularChainFunctor R).map (TopCat.ofHom e.toFun)
  inv := (singularChainFunctor R).map (TopCat.ofHom e.invFun)
  homotopyHomInvId := by
    rw [← Functor.map_comp]
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap (X := TopCat.of X) (Y := TopCat.of X)
      (f := TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (g := 𝟙 _)
      (Classical.choice e.left_inv) R).trans (Homotopy.ofEq (by simp))
  homotopyInvHomId := by
    rw [← Functor.map_comp]
    exact (TopCat.Homotopy.singularChainComplexFunctorObjMap (X := TopCat.of Y) (Y := TopCat.of Y)
      (f := TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (g := 𝟙 _)
      (Classical.choice e.right_inv) R).trans (Homotopy.ofEq (by simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.chainHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.chainHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.chainHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.chainHomotopyEquiv

def homologyIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) : singularHomology R (TopCat.of X) n ≅ singularHomology R (TopCat.of Y) n :=
  haveI : _root_.CategoryTheory.IsIso (_root_.HomologicalComplex.homologyMap (chainHomotopyEquiv R e).hom n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  @_root_.CategoryTheory.asIso _ _ _ _ _ this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyIso ``Submission.DifferentialGeometry.Topology.SingularPair.homologyIso

theorem isZero_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of X) n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let e' : ContinuousMap.HomotopyEquiv X PUnit.{u + 1} :=
    e.trans (Homeomorph.homeomorphOfUnique Unit PUnit.{u + 1}).toHomotopyEquiv
  have h1 : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of PUnit.{u + 1}) n) :=
    _root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ n R (TopCat.of PUnit.{u + 1}) hn
  have h2 : singularHomology R (TopCat.of X) n ≅ singularHomology R (TopCat.of PUnit.{u + 1}) n := homologyIso R e' n
  exact h1.of_iso h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_of_contractible ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_of_contractible

end DifferentialGeometry.Topology.SingularPair
