import Submission.DifferentialGeometry.Topology.Homology.SingularPair
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.AlgebraicTopology _root_.HomologicalComplex _root_.Submission.HomologicalComplex _root_.Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

abbrev singularHomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) : singularHomology R X n ⟶ singularHomology R Y n :=
  ((_root_.AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj R).map f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyMap

lemma singularHomologyMap_eq_homologyMap {X Y : TopCat.{u}} (f : X ⟶ Y) (n : ℕ) :
    singularHomologyMap R f n = _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map f) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_eq_homologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyMap_eq_homologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_eq_homologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyMap_eq_homologyMap

lemma singularHomologyMap_id (X : TopCat.{u}) (n : ℕ) : singularHomologyMap R (𝟙 X) n = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_id ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyMap_id

@[reassoc]
lemma singularHomologyMap_comp {X Y W : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ W) (n : ℕ) :
    singularHomologyMap R (f ≫ g) n = singularHomologyMap R f n ≫ singularHomologyMap R g n :=
  CategoryTheory.Functor.map_comp _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_comp ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyMap_comp

lemma inclMap_eq_singularHomologyMap (X : TopCat.{u}) (A : Set X) (n : ℕ) :
    inclMap R X A n = singularHomologyMap R (incl X A) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclMap_eq_singularHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclMap_eq_singularHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclMap_eq_singularHomologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.inclMap_eq_singularHomologyMap

lemma homologyIso_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (homologyIso R e n).hom = singularHomologyMap R (TopCat.ofHom e.toFun) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.homologyIso_hom

instance isIso_singularHomologyMap_of_homotopyEquiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    IsIso (singularHomologyMap R (TopCat.ofHom e.toFun) n) :=
  ⟨(homologyIso R e n).inv, (homologyIso R e n).hom_inv_id, (homologyIso R e n).inv_hom_id⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_of_homotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_of_homotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_of_homotopyEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_singularHomologyMap_of_homotopyEquiv

def restr {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨hf.restrict, by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restr ``Submission.DifferentialGeometry.Topology.SingularPair.restr

@[simp]
lemma restr_apply {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (a : A) : restr f hf a = ⟨f a, hf a.2⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restr_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restr_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restr_apply ``Submission.DifferentialGeometry.Topology.SingularPair.restr_apply

lemma restr_comp_incl {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : restr f hf ≫ incl Y B = incl X A ≫ f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restr_comp_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restr_comp_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restr_comp_incl ``Submission.DifferentialGeometry.Topology.SingularPair.restr_comp_incl

lemma pairMap_left {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : (pairMap f hf).left = TopCat.toSSet.map (restr f hf) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_left ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_left

lemma pairMap_right {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) : (pairMap f hf).right = TopCat.toSSet.map f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_right ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_right

lemma restr_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) :
    restr (𝟙 X) hf = 𝟙 (TopCat.of A) := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restr_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restr_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restr_id ``Submission.DifferentialGeometry.Topology.SingularPair.restr_id

lemma restr_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) :
    restr (f ≫ g) hfg = restr f hf ≫ restr g hg := by
  ext x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restr_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restr_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restr_comp ``Submission.DifferentialGeometry.Topology.SingularPair.restr_comp

lemma pairMap_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) :
    pairMap (𝟙 X) hf = 𝟙 (pair X A) := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change TopCat.toSSet.map (restr (𝟙 X) hf) = 𝟙 _
    rw [restr_id, CategoryTheory.Functor.map_id]
  · rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_id ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_id

lemma pairMap_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) :
    pairMap (f ≫ g) hfg = pairMap f hf ≫ pairMap g hg := by
  refine MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)
  · change TopCat.toSSet.map (restr (f ≫ g) hfg) =
      TopCat.toSSet.map (restr f hf) ≫ TopCat.toSSet.map (restr g hg)
    rw [restr_comp f g hf hg hfg, CategoryTheory.Functor.map_comp]
  · change TopCat.toSSet.map (f ≫ g) = TopCat.toSSet.map f ≫ TopCat.toSSet.map g
    rw [CategoryTheory.Functor.map_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_comp ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_comp

theorem relativeHomologyMap_id (X : TopCat.{u}) (A : Set X) (hf : Set.MapsTo (𝟙 X) A A) (n : ℕ) :
    relativeHomologyMap R (𝟙 X) hf n = 𝟙 _ := by
  rw [relativeHomologyMap, pairMap_id, SSetPair.homologyMap_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id

theorem relativeHomologyMap_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W}
    (f : X ⟶ Y) (g : Y ⟶ W) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D)
    (hfg : Set.MapsTo (f ≫ g) A D) (n : ℕ) :
    relativeHomologyMap R (f ≫ g) hfg n = relativeHomologyMap R f hf n ≫ relativeHomologyMap R g hg n := by
  rw [relativeHomologyMap, pairMap_comp f g hf hg hfg, SSetPair.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp

@[reassoc (attr := simp)]
lemma relativeHomologyMap_id_comp {X : TopCat.{u}} {A B D : Set X}
    (hAB : Set.MapsTo (𝟙 X) A B) (hBD : Set.MapsTo (𝟙 X) B D) (n : ℕ) :
    relativeHomologyMap R (𝟙 X) hAB n ≫ relativeHomologyMap R (𝟙 X) hBD n =
      relativeHomologyMap R (𝟙 X) (fun _ hx => hBD (hAB hx)) n := by
  simpa only [Category.id_comp] using
    (relativeHomologyMap_comp R (𝟙 X) (𝟙 X) hAB hBD (fun _ hx => hBD (hAB hx)) n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id_comp ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_id_comp

def scMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y) (hf : Set.MapsTo f A B) :
    (pair X A).chainComplexShortComplex R ⟶ (pair Y B).chainComplexShortComplex R where
  τ₁ := (singularChainFunctor R).map (restr f hf)
  τ₂ := (singularChainFunctor R).map f
  τ₃ := SSetPair.chainComplexMap (pairMap f hf) R
  comm₁₂ := ((SSetPair.chainComplexFunctorLeftToRight _).app R).naturality (pairMap f hf)
  comm₂₃ := ((SSetPair.chainComplexFunctorπ _).app R).naturality (pairMap f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.scMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.scMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.scMap ``Submission.DifferentialGeometry.Topology.SingularPair.scMap

theorem δ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    δ R X A n ≫ singularHomologyMap R (restr f hf) n = relativeHomologyMap R f hf (n + 1) ≫ δ R Y B n :=
  HomologySequence.δ_naturality (scMap R f hf) _ _ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ_natural ``Submission.DifferentialGeometry.Topology.SingularPair.δ_natural

theorem δ_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    δ R X A n ≫ _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (restr f hf)) n = relativeHomologyMap R f hf (n + 1) ≫ δ R Y B n :=
  δ_natural R f hf n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ_natural' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ_natural'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ_natural' ``Submission.DifferentialGeometry.Topology.SingularPair.δ_natural'

lemma chainComplexπ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) :
    ((SSetPair.chainComplexFunctorRight _).obj R).map (pairMap f hf) ≫
      ((SSetPair.chainComplexFunctorπ _).app R).app (pair Y B) =
    ((SSetPair.chainComplexFunctorπ _).app R).app (pair X A) ≫
      ((SSetPair.chainComplexFunctor _).obj R).map (pairMap f hf) :=
  ((SSetPair.chainComplexFunctorπ _).app R).naturality (pairMap f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.chainComplexπ_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.chainComplexπ_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.chainComplexπ_natural ``Submission.DifferentialGeometry.Topology.SingularPair.chainComplexπ_natural

theorem relπ_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    relπ R X A n ≫ relativeHomologyMap R f hf n = singularHomologyMap R f n ≫ relπ R Y B n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chainComplexπ_natural R f hf)
  simp only [_root_.HomologicalComplex.homologyMap_comp] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relπ_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relπ_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relπ_natural ``Submission.DifferentialGeometry.Topology.SingularPair.relπ_natural

theorem relπ_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    relπ R X A n ≫ relativeHomologyMap R f hf n = _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map f) n ≫ relπ R Y B n :=
  relπ_natural R f hf n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relπ_natural' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relπ_natural'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relπ_natural' ``Submission.DifferentialGeometry.Topology.SingularPair.relπ_natural'

theorem inclMap_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    inclMap R X A n ≫ singularHomologyMap R f n = singularHomologyMap R (restr f hf) n ≫ inclMap R Y B n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (((SSetPair.chainComplexFunctorLeftToRight _).app R).naturality (pairMap f hf))
  simp only [_root_.HomologicalComplex.homologyMap_comp] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclMap_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclMap_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclMap_natural ``Submission.DifferentialGeometry.Topology.SingularPair.inclMap_natural

theorem inclMap_natural' {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (n : ℕ) :
    inclMap R X A n ≫ _root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map f) n =
      homologyMap ((singularChainFunctor R).map (restr f hf)) n ≫ inclMap R Y B n :=
  inclMap_natural R f hf n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclMap_natural' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclMap_natural'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclMap_natural' ``Submission.DifferentialGeometry.Topology.SingularPair.inclMap_natural'

abbrev ε (X : TopCat.{u}) : singularHomology R X 0 ⟶ R := X.singularHomology₀ε R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ε ``Submission.DifferentialGeometry.Topology.SingularPair.ε

@[reassoc]
lemma ι_inv_iCycles (X : SSet.{u}) (x : X _⦋0⦌) :
    X.ιChainComplex x ≫ _root_.CategoryTheory.inv ((X.chainComplex R).iCycles 0) =
      (X.chainComplex R).liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) := by
  rw [← _root_.CategoryTheory.cancel_mono ((X.chainComplex R).iCycles 0)]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_inv_iCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_inv_iCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_inv_iCycles ``Submission.DifferentialGeometry.Topology.SingularPair.ι_inv_iCycles

lemma homology₀ε_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  rw [SSet.homologyMap, ← _root_.CategoryTheory.cancel_epi ((X.chainComplex R).homologyπ 0), _root_.HomologicalComplex.homologyπ_naturality_assoc,
    ← _root_.CategoryTheory.cancel_epi (_root_.CategoryTheory.inv ((X.chainComplex R).iCycles 0))]
  apply SSet.chainComplex_hom_ext
  intro x
  rw [ι_inv_iCycles_assoc, ι_inv_iCycles_assoc, _root_.HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homology₀ε_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homology₀ε_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homology₀ε_natural ``Submission.DifferentialGeometry.Topology.SingularPair.homology₀ε_natural

@[reassoc (attr := simp)]
theorem ε_natural {X Y : TopCat.{u}} (f : X ⟶ Y) : singularHomologyMap R f 0 ≫ ε R Y = ε R X :=
  homology₀ε_natural R (TopCat.toSSet.map f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ε_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ε_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ε_natural ``Submission.DifferentialGeometry.Topology.SingularPair.ε_natural

theorem ε_natural' {X Y : TopCat.{u}} (f : X ⟶ Y) :
    homologyMap ((singularChainFunctor R).map f) 0 ≫ Y.singularHomology₀ε R = X.singularHomology₀ε R :=
  ε_natural R f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ε_natural' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ε_natural'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ε_natural' ``Submission.DifferentialGeometry.Topology.SingularPair.ε_natural'

@[reassoc (attr := simp)]
theorem inclMap_ε (X : TopCat.{u}) (A : Set X) : inclMap R X A 0 ≫ ε R X = ε R (TopCat.of A) :=
  ε_natural R (incl X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclMap_ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclMap_ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclMap_ε ``Submission.DifferentialGeometry.Topology.SingularPair.inclMap_ε

theorem isIso_ε_of_pathConnected (X : TopCat.{u}) [PathConnectedSpace X] : _root_.CategoryTheory.IsIso (ε R X) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_ε_of_pathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_ε_of_pathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_ε_of_pathConnected ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_ε_of_pathConnected

theorem isIso_ε_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    IsIso (ε R (TopCat.of X)) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_ε_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_ε_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_ε_of_contractible ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_ε_of_contractible

abbrev reducedHomologyZero (X : TopCat.{u}) : ModuleCat.{u} ℤ := _root_.CategoryTheory.Limits.kernel (ε R X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZero ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZero

abbrev reducedHomologyZeroInclusion (X : TopCat.{u}) : reducedHomologyZero R X ⟶ singularHomology R X 0 := kernel.ι (ε R X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion

instance _root_.Submission.DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntReducedHomologyZeroInclusion (X : TopCat.{u}) : _root_.CategoryTheory.Mono (reducedHomologyZeroInclusion R X) := inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntReducedHomologyZeroInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntReducedHomologyZeroInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntReducedHomologyZeroInclusion ``Submission.DifferentialGeometry.Topology.SingularPair.instMonoModuleCatIntReducedHomologyZeroInclusion

@[reassoc]
lemma reducedHomologyZeroInclusion_ε (X : TopCat.{u}) : reducedHomologyZeroInclusion R X ≫ ε R X = 0 := kernel.condition _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion_ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion_ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion_ε ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroInclusion_ε

def reducedHomologyZeroMap {X Y : TopCat.{u}} (f : X ⟶ Y) : reducedHomologyZero R X ⟶ reducedHomologyZero R Y :=
  kernel.lift _ (reducedHomologyZeroInclusion R X ≫ singularHomologyMap R f 0) (by rw [Category.assoc, ε_natural, kernel.condition])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap

@[reassoc (attr := simp)]
lemma reducedHomologyZeroMap_ι {X Y : TopCat.{u}} (f : X ⟶ Y) :
    reducedHomologyZeroMap R f ≫ reducedHomologyZeroInclusion R Y = reducedHomologyZeroInclusion R X ≫ singularHomologyMap R f 0 :=
  kernel.lift_ι _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_ι ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_ι

@[simp]
lemma reducedHomologyZeroMap_id (X : TopCat.{u}) : reducedHomologyZeroMap R (𝟙 X) = 𝟙 _ := by
  rw [← _root_.CategoryTheory.cancel_mono (reducedHomologyZeroInclusion R X), reducedHomologyZeroMap_ι, singularHomologyMap_id, Category.comp_id, Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_id ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_id

@[reassoc]
lemma reducedHomologyZeroMap_comp {X Y W : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ W) :
    reducedHomologyZeroMap R (f ≫ g) = reducedHomologyZeroMap R f ≫ reducedHomologyZeroMap R g := by
  rw [← _root_.CategoryTheory.cancel_mono (reducedHomologyZeroInclusion R W), reducedHomologyZeroMap_ι, singularHomologyMap_comp, Category.assoc, reducedHomologyZeroMap_ι,
    reducedHomologyZeroMap_ι_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp

lemma mono_reducedHomologyZeroMap_of_mono {X Y : TopCat.{u}} (f : X ⟶ Y) [_root_.CategoryTheory.Mono (singularHomologyMap R f 0)] :
    Mono (reducedHomologyZeroMap R f) :=
  _root_.CategoryTheory.mono_of_mono_fac (reducedHomologyZeroMap_ι R f)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mono_reducedHomologyZeroMap_of_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mono_reducedHomologyZeroMap_of_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mono_reducedHomologyZeroMap_of_mono ``Submission.DifferentialGeometry.Topology.SingularPair.mono_reducedHomologyZeroMap_of_mono

def reducedHomologyZeroMapIso {X Y : TopCat.{u}} (f : X ⟶ Y) [_root_.CategoryTheory.IsIso (singularHomologyMap R f 0)] : reducedHomologyZero R X ≅ reducedHomologyZero R Y :=
  kernel.mapIso (ε R X) (ε R Y) (_root_.CategoryTheory.asIso (singularHomologyMap R f 0)) (Iso.refl R)
    (by rw [Iso.refl_hom, Category.comp_id, _root_.CategoryTheory.asIso_hom, ε_natural])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso

lemma reducedHomologyZeroMapIso_hom {X Y : TopCat.{u}} (f : X ⟶ Y) [_root_.CategoryTheory.IsIso (singularHomologyMap R f 0)] :
    (reducedHomologyZeroMapIso R f).hom = reducedHomologyZeroMap R f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMapIso_hom

instance isIso_reducedHomologyZeroMap {X Y : TopCat.{u}} (f : X ⟶ Y) [_root_.CategoryTheory.IsIso (singularHomologyMap R f 0)] :
    IsIso (reducedHomologyZeroMap R f) :=
  ⟨(reducedHomologyZeroMapIso R f).inv, (reducedHomologyZeroMapIso R f).hom_inv_id, (reducedHomologyZeroMapIso R f).inv_hom_id⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_reducedHomologyZeroMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_reducedHomologyZeroMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_reducedHomologyZeroMap ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_reducedHomologyZeroMap

def reducedHomologyZeroIso {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) : reducedHomologyZero R (TopCat.of X) ≅ reducedHomologyZero R (TopCat.of Y) :=
  reducedHomologyZeroMapIso R (TopCat.ofHom e.toFun)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso

lemma reducedHomologyZeroIso_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    (reducedHomologyZeroIso R e).hom = reducedHomologyZeroMap R (TopCat.ofHom e.toFun) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIso_hom

def reducedHomologyZeroIsoOfHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    reducedHomologyZero R (TopCat.of X) ≅ reducedHomologyZero R (TopCat.of Y) :=
  reducedHomologyZeroIso R e.toHomotopyEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfHomeomorph ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfHomeomorph

theorem isZero_reducedHomologyZero_of_pathConnected (X : TopCat.{u}) [PathConnectedSpace X] :
    IsZero (reducedHomologyZero R X) :=
  (_root_.CategoryTheory.Limits.isZero_zero _).of_iso (kernel.ofMono (ε R X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_pathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_pathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_pathConnected ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_pathConnected

theorem isZero_reducedHomologyZero_of_contractible (X : Type u) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (reducedHomologyZero R (TopCat.of X)) :=
  isZero_reducedHomologyZero_of_pathConnected R (TopCat.of X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_contractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_contractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_contractible ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_reducedHomologyZero_of_contractible

section two

variable {ι : Type u} (a b : ι)

def prj (c : ι) : ∐ (fun _ : ι ↦ R) ⟶ R := by
  classical
  exact Sigma.desc (fun i ↦ if i = c then 𝟙 R else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.prj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.prj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.prj ``Submission.DifferentialGeometry.Topology.SingularPair.prj

@[reassoc (attr := simp)]
lemma ι_prj_self (c : ι) : Sigma.ι (fun _ : ι ↦ R) c ≫ prj R c = 𝟙 R := by
  simp [prj]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_prj_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_prj_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_prj_self ``Submission.DifferentialGeometry.Topology.SingularPair.ι_prj_self

@[reassoc]
lemma ι_prj_ne {i c : ι} (h : i ≠ c) : Sigma.ι (fun _ : ι ↦ R) i ≫ prj R c = 0 := by
  simp [prj, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_prj_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_prj_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_prj_ne ``Submission.DifferentialGeometry.Topology.SingularPair.ι_prj_ne

lemma sub_comp_sigmaDesc_id :
    (Sigma.ι (fun _ : ι ↦ R) a - Sigma.ι (fun _ : ι ↦ R) b) ≫ Sigma.desc (fun _ : ι ↦ 𝟙 R) = 0 := by
  simp [Preadditive.sub_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.sub_comp_sigmaDesc_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.sub_comp_sigmaDesc_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.sub_comp_sigmaDesc_id ``Submission.DifferentialGeometry.Topology.SingularPair.sub_comp_sigmaDesc_id

variable (hab : a ≠ b) (hcov : ∀ i, i = a ∨ i = b)
include hab hcov

lemma prj_total : prj R a ≫ Sigma.ι (fun _ : ι ↦ R) a + prj R b ≫ Sigma.ι (fun _ : ι ↦ R) b =
    𝟙 _ := by
  ext i
  rcases hcov i with rfl | rfl
  · simp [Preadditive.comp_add, ι_prj_ne_assoc R hab]
  · simp [Preadditive.comp_add, ι_prj_ne_assoc R hab.symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.prj_total then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.prj_total"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.prj_total ``Submission.DifferentialGeometry.Topology.SingularPair.prj_total

lemma sigmaDesc_id_eq : Sigma.desc (fun _ : ι ↦ 𝟙 R) = prj R a + prj R b := by
  ext i
  rcases hcov i with rfl | rfl
  · simp [Preadditive.comp_add, ι_prj_ne R hab]
  · simp [Preadditive.comp_add, ι_prj_ne R hab.symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.sigmaDesc_id_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.sigmaDesc_id_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.sigmaDesc_id_eq ``Submission.DifferentialGeometry.Topology.SingularPair.sigmaDesc_id_eq

def isLimitKernelForkTwo :
    IsLimit (KernelFork.ofι _ (sub_comp_sigmaDesc_id R a b)) :=
  KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ prj R a)
    (fun g hg ↦ by
      have h1 : g ≫ prj R a + g ≫ prj R b = 0 := by
        rw [← Preadditive.comp_add, ← sigmaDesc_id_eq R a b hab hcov, hg]
      have h2 : g ≫ prj R b = -(g ≫ prj R a) := by
        rw [eq_neg_iff_add_eq_zero, add_comm, h1]
      calc (g ≫ prj R a) ≫ (Sigma.ι (fun _ : ι ↦ R) a - Sigma.ι (fun _ : ι ↦ R) b)
          = g ≫ prj R a ≫ Sigma.ι (fun _ : ι ↦ R) a + g ≫ prj R b ≫ Sigma.ι (fun _ : ι ↦ R) b := by
            rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, h2,
              Preadditive.neg_comp, sub_eq_add_neg]
        _ = g := by
            rw [← Preadditive.comp_add, prj_total R a b hab hcov, Category.comp_id])
    (fun g hg m hm ↦ by
      rw [← hm, Category.assoc, Preadditive.sub_comp, ι_prj_self, ι_prj_ne R hab.symm, sub_zero,
        Category.comp_id])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isLimitKernelForkTwo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isLimitKernelForkTwo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isLimitKernelForkTwo ``Submission.DifferentialGeometry.Topology.SingularPair.isLimitKernelForkTwo

def kernelSigmaDescTwoIso : _root_.CategoryTheory.Limits.kernel (Sigma.desc (fun _ : ι ↦ 𝟙 R)) ≅ R :=
  (_root_.CategoryTheory.Limits.kernelIsKernel _).conePointUniqueUpToIso (isLimitKernelForkTwo R a b hab hcov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.kernelSigmaDescTwoIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.kernelSigmaDescTwoIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.kernelSigmaDescTwoIso ``Submission.DifferentialGeometry.Topology.SingularPair.kernelSigmaDescTwoIso

end two

def reducedHomologyZeroIsoKernelSigmaDesc (X : TopCat.{u}) :
    reducedHomologyZero R X ≅ _root_.CategoryTheory.Limits.kernel (Sigma.desc (fun _ : ZerothHomotopy X ↦ 𝟙 R)) :=
  kernel.mapIso (ε R X) _ (X.singularHomology₀Iso R) (Iso.refl R)
    (by rw [Iso.refl_hom, Category.comp_id, TopCat.singularHomology₀Iso_sigma_desc_id])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoKernelSigmaDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoKernelSigmaDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoKernelSigmaDesc ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoKernelSigmaDesc

def reducedHomologyZeroIsoOfTwoPathComponents (X : TopCat.{u}) (a b : ZerothHomotopy X) (hab : a ≠ b)
    (hcov : ∀ i, i = a ∨ i = b) : reducedHomologyZero R X ≅ R :=
  reducedHomologyZeroIsoKernelSigmaDesc R X ≪≫ kernelSigmaDescTwoIso R a b hab hcov

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPathComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPathComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPathComponents ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPathComponents

open _root_.ZerothHomotopy in
lemma _root_.Submission.ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace {X : Type u}
    [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    Function.Injective (ZerothHomotopy.mk (X := X)) := by
  intro x y h
  obtain ⟨p⟩ : Joined x y := Quotient.exact h
  exact (isPreconnected_range p.continuous).subsingleton ⟨0, p.source⟩ ⟨1, p.target⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ZerothHomotopy
  let env ← Lean.getEnv
  if env.contains `ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace then
    throwError "Refusing to shadow existing declaration ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace ``Submission.ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace

open _root_.ZerothHomotopy in
def _root_.Submission.ZerothHomotopy.equivOfTotallyDisconnectedSpace (X : Type u) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : X ≃ ZerothHomotopy X :=
  Equiv.ofBijective ZerothHomotopy.mk
    ⟨ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace, ZerothHomotopy.mk_surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ZerothHomotopy.equivOfTotallyDisconnectedSpace then
    throwError "Refusing to shadow existing declaration ZerothHomotopy.equivOfTotallyDisconnectedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `ZerothHomotopy.equivOfTotallyDisconnectedSpace ``Submission.ZerothHomotopy.equivOfTotallyDisconnectedSpace

def reducedHomologyZeroIsoOfTwoPoints (X : TopCat.{u}) [TotallyDisconnectedSpace X] (x y : X) (hxy : x ≠ y)
    (hcov : ∀ z, z = x ∨ z = y) : reducedHomologyZero R X ≅ R :=
  reducedHomologyZeroIsoOfTwoPathComponents R X (.mk x) (.mk y)
    (fun h ↦ hxy (ZerothHomotopy.mk_injective_of_totallyDisconnectedSpace h))
    (fun i ↦ by
      obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective i
      rcases hcov z with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPoints ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroIsoOfTwoPoints

def reducedHomologyZeroUliftFinTwoIso : reducedHomologyZero R (TopCat.of (ULift.{u} (Fin 2))) ≅ R :=
  reducedHomologyZeroIsoOfTwoPoints R (TopCat.of (ULift.{u} (Fin 2))) ⟨0⟩ ⟨1⟩ (by simp)
    (fun z ↦ by
      rcases z with ⟨z⟩
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroUliftFinTwoIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroUliftFinTwoIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroUliftFinTwoIso ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroUliftFinTwoIso

section kernelExact

variable {S : ShortComplex (ModuleCat.{u} ℤ)} (hS : S.Exact)

lemma kernelLift_comp_zero₃ {T : ModuleCat.{u} ℤ} (ε₃ : S.X₃ ⟶ T) (h : S.g ≫ ε₃ = 0) :
    S.f ≫ kernel.lift ε₃ S.g h = 0 := by
  rw [← _root_.CategoryTheory.cancel_mono (kernel.ι ε₃), Category.assoc, kernel.lift_ι, S.zero, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₃ ``Submission.DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₃

include hS in
lemma exact_kernelLift₃ {T : ModuleCat.{u} ℤ} (ε₃ : S.X₃ ⟶ T) (h : S.g ≫ ε₃ = 0) :
    (ShortComplex.mk S.f (kernel.lift ε₃ S.g h) (kernelLift_comp_zero₃ ε₃ h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change kernel.lift ε₃ S.g h x₂ = 0 at hx₂
  apply hS
  have := congrArg (kernel.ι ε₃) hx₂
  rwa [← ModuleCat.comp_apply, kernel.lift_ι, map_zero] at this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exact_kernelLift₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exact_kernelLift₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exact_kernelLift₃ ``Submission.DifferentialGeometry.Topology.SingularPair.exact_kernelLift₃

section
variable {T₂ T₃ : ModuleCat.{u} ℤ} (ε₂ : S.X₂ ⟶ T₂) (ε₃ : S.X₃ ⟶ T₃) (t : T₂ ⟶ T₃) [Mono t]
  (h : S.g ≫ ε₃ = ε₂ ≫ t)
include h

lemma f_comp_eq_zero_of_mono : S.f ≫ ε₂ = 0 := by
  rw [← _root_.CategoryTheory.cancel_mono t, Category.assoc, ← h, ← Category.assoc, S.zero, _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.f_comp_eq_zero_of_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.f_comp_eq_zero_of_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.f_comp_eq_zero_of_mono ``Submission.DifferentialGeometry.Topology.SingularPair.f_comp_eq_zero_of_mono

omit [Mono t] in
lemma ι_comp_g_comp_eq_zero : (kernel.ι ε₂ ≫ S.g) ≫ ε₃ = 0 := by
  rw [Category.assoc, h, kernel.condition_assoc, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_comp_g_comp_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_comp_g_comp_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_comp_g_comp_eq_zero ``Submission.DifferentialGeometry.Topology.SingularPair.ι_comp_g_comp_eq_zero

lemma kernelLift_comp_zero₂₃ :
    kernel.lift ε₂ S.f (f_comp_eq_zero_of_mono ε₂ ε₃ t h) ≫
      kernel.lift ε₃ (kernel.ι ε₂ ≫ S.g) (ι_comp_g_comp_eq_zero ε₂ ε₃ t h) = 0 := by
  rw [← _root_.CategoryTheory.cancel_mono (kernel.ι ε₃), Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, S.zero,
    _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₂₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₂₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₂₃ ``Submission.DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₂₃

include hS in
lemma exact_kernelLift₂₃ :
    (ShortComplex.mk _ _ (kernelLift_comp_zero₂₃ ε₂ ε₃ t h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change kernel.lift ε₃ (kernel.ι ε₂ ≫ S.g) _ x₂ = 0 at hx₂
  have h1 : S.g (kernel.ι ε₂ x₂) = 0 := by
    have := congrArg (kernel.ι ε₃) hx₂
    rwa [← ModuleCat.comp_apply, kernel.lift_ι, map_zero, ModuleCat.comp_apply] at this
  obtain ⟨x₁, hx₁⟩ := hS _ h1
  refine ⟨x₁, ?_⟩
  apply (ModuleCat.mono_iff_injective (kernel.ι ε₂)).1 inferInstance
  change (kernel.lift ε₂ S.f _ ≫ kernel.ι ε₂) x₁ = kernel.ι ε₂ x₂
  rw [kernel.lift_ι]
  exact hx₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exact_kernelLift₂₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exact_kernelLift₂₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exact_kernelLift₂₃ ``Submission.DifferentialGeometry.Topology.SingularPair.exact_kernelLift₂₃

end

section
variable {T₁ T₂ : ModuleCat.{u} ℤ} (ε₁ : S.X₁ ⟶ T₁) (ε₂ : S.X₂ ⟶ T₂) (t : T₁ ⟶ T₂) [Mono t]
  (h : S.f ≫ ε₂ = ε₁ ≫ t)
include h

omit [Mono t] in
lemma ι_comp_f_comp_eq_zero : (kernel.ι ε₁ ≫ S.f) ≫ ε₂ = 0 := by
  rw [Category.assoc, h, kernel.condition_assoc, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ι_comp_f_comp_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ι_comp_f_comp_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ι_comp_f_comp_eq_zero ``Submission.DifferentialGeometry.Topology.SingularPair.ι_comp_f_comp_eq_zero

omit [Mono t] in
lemma kernelLift_comp_zero₁₂ :
    kernel.lift ε₂ (kernel.ι ε₁ ≫ S.f) (ι_comp_f_comp_eq_zero ε₁ ε₂ t h) ≫
      (kernel.ι ε₂ ≫ S.g) = 0 := by
  rw [kernel.lift_ι_assoc, Category.assoc, S.zero, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₁₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₁₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₁₂ ``Submission.DifferentialGeometry.Topology.SingularPair.kernelLift_comp_zero₁₂

include hS in
lemma exact_kernelLift₁₂ :
    (ShortComplex.mk _ _ (kernelLift_comp_zero₁₂ ε₁ ε₂ t h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
  intro x₂ hx₂
  change (kernel.ι ε₂ ≫ S.g) x₂ = 0 at hx₂
  rw [ModuleCat.comp_apply] at hx₂
  obtain ⟨x₁, hx₁⟩ := hS _ hx₂
  have hx₁' : ε₁ x₁ = 0 := by
    apply (ModuleCat.mono_iff_injective t).1 inferInstance
    rw [map_zero]
    calc t (ε₁ x₁) = (S.f ≫ ε₂) x₁ := by rw [h, ModuleCat.comp_apply]
      _ = ε₂ (kernel.ι ε₂ x₂) := by rw [ModuleCat.comp_apply, hx₁]
      _ = (kernel.ι ε₂ ≫ ε₂) x₂ := by rw [ModuleCat.comp_apply]
      _ = 0 := by rw [kernel.condition]; simp
  let y := (ModuleCat.kernelIsoKer ε₁).inv ⟨x₁, LinearMap.mem_ker.2 hx₁'⟩
  have hy : kernel.ι ε₁ y = x₁ := by
    change ((ModuleCat.kernelIsoKer ε₁).inv ≫ kernel.ι ε₁) ⟨x₁, _⟩ = x₁
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    rfl
  refine ⟨y, ?_⟩
  apply (ModuleCat.mono_iff_injective (kernel.ι ε₂)).1 inferInstance
  change (kernel.lift ε₂ (kernel.ι ε₁ ≫ S.f) _ ≫ kernel.ι ε₂) y = kernel.ι ε₂ x₂
  rw [kernel.lift_ι, ModuleCat.comp_apply, hy, hx₁]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.exact_kernelLift₁₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.exact_kernelLift₁₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.exact_kernelLift₁₂ ``Submission.DifferentialGeometry.Topology.SingularPair.exact_kernelLift₁₂

end

end kernelExact

variable (X : TopCat.{u}) (A : Set X)

@[reassoc (attr := simp)]
theorem δ_comp_ε : δ R X A 0 ≫ ε R (TopCat.of A) = 0 := by
  have h : δ R X A 0 ≫ inclMap R X A 0 = 0 := (pair X A).homologyδ_comp R 1 0 rfl
  rw [← inclMap_ε, ← Category.assoc, h, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δ_comp_ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δ_comp_ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δ_comp_ε ``Submission.DifferentialGeometry.Topology.SingularPair.δ_comp_ε

def δred : relativeHomology R X A 1 ⟶ reducedHomologyZero R (TopCat.of A) :=
  kernel.lift _ (δ R X A 0) (δ_comp_ε R X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δred ``Submission.DifferentialGeometry.Topology.SingularPair.δred

@[reassoc (attr := simp)]
lemma δred_ι : δred R X A ≫ reducedHomologyZeroInclusion R (TopCat.of A) = δ R X A 0 :=
  kernel.lift_ι _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δred_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δred_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δred_ι ``Submission.DifferentialGeometry.Topology.SingularPair.δred_ι

@[reassoc (attr := simp)]
lemma δred_comp_reducedHomologyZeroMap : δred R X A ≫ reducedHomologyZeroMap R (incl X A) = 0 := by
  rw [← _root_.CategoryTheory.cancel_mono (reducedHomologyZeroInclusion R X), Category.assoc, reducedHomologyZeroMap_ι, δred_ι_assoc, _root_.CategoryTheory.Limits.zero_comp]
  exact (pair X A).homologyδ_comp R 1 0 rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δred_comp_reducedHomologyZeroMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δred_comp_reducedHomologyZeroMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δred_comp_reducedHomologyZeroMap ``Submission.DifferentialGeometry.Topology.SingularPair.δred_comp_reducedHomologyZeroMap

@[reassoc (attr := simp)]
lemma singularHomologyMap_incl_relπ (n : ℕ) :
    singularHomologyMap R (incl X A) n ≫ relπ R X A n = 0 :=
  (pair X A).homologyMap_hom_homologyπ R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_incl_relπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyMap_incl_relπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyMap_incl_relπ ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyMap_incl_relπ

@[reassoc]
lemma reducedHomologyZeroMap_comp_relπ : reducedHomologyZeroMap R (incl X A) ≫ (reducedHomologyZeroInclusion R X ≫ relπ R X A 0) = 0 := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp_relπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp_relπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp_relπ ``Submission.DifferentialGeometry.Topology.SingularPair.reducedHomologyZeroMap_comp_relπ

@[reassoc (attr := simp)]
lemma relπ_comp_δred : relπ R X A 1 ≫ δred R X A = 0 := by
  rw [← _root_.CategoryTheory.cancel_mono (reducedHomologyZeroInclusion R (TopCat.of A)), Category.assoc, δred_ι, _root_.CategoryTheory.Limits.zero_comp]
  exact (pair X A).comp_homologyδ R 1 0 rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relπ_comp_δred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relπ_comp_δred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relπ_comp_δred ``Submission.DifferentialGeometry.Topology.SingularPair.relπ_comp_δred

theorem les_red_exact₁ :
    (ShortComplex.mk (δred R X A) (reducedHomologyZeroMap R (incl X A)) (δred_comp_reducedHomologyZeroMap R X A)).Exact :=
  exact_kernelLift₂₃ (les_exact₁ R X A 0) (ε R (TopCat.of A)) (ε R X) (𝟙 R)
    (by rw [Category.comp_id]; exact inclMap_ε R X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.les_red_exact₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.les_red_exact₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.les_red_exact₁ ``Submission.DifferentialGeometry.Topology.SingularPair.les_red_exact₁

theorem les_red_exact₂ :
    (ShortComplex.mk (reducedHomologyZeroMap R (incl X A)) (reducedHomologyZeroInclusion R X ≫ relπ R X A 0)
      (reducedHomologyZeroMap_comp_relπ R X A)).Exact :=
  exact_kernelLift₁₂ (les_exact₂ R X A 0) (ε R (TopCat.of A)) (ε R X) (𝟙 R)
    (by rw [Category.comp_id]; exact inclMap_ε R X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.les_red_exact₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.les_red_exact₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.les_red_exact₂ ``Submission.DifferentialGeometry.Topology.SingularPair.les_red_exact₂

theorem les_red_exact₃ :
    (ShortComplex.mk (relπ R X A 1) (δred R X A) (relπ_comp_δred R X A)).Exact :=
  exact_kernelLift₃ (les_exact₃ R X A 0) (ε R (TopCat.of A)) (δ_comp_ε R X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.les_red_exact₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.les_red_exact₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.les_red_exact₃ ``Submission.DifferentialGeometry.Topology.SingularPair.les_red_exact₃

end DifferentialGeometry.Topology.SingularPair
