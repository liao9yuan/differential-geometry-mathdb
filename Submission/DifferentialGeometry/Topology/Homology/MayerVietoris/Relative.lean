import Submission.DifferentialGeometry.Topology.Homology.MayerVietoris.ShortExact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.Simplicial _root_.Opposite _root_.HomologicalComplex _root_.Submission.HomologicalComplex

open scoped _root_.ZeroObject

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

section BiprodCofork

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} {f₁ : X₁ ⟶ Y₁} {π₁ : Y₁ ⟶ Z₁} {f₂ : X₂ ⟶ Y₂} {π₂ : Y₂ ⟶ Z₂}

lemma biprod_map_map_condition (w₁ : f₁ ≫ π₁ = 0) (w₂ : f₂ ≫ π₂ = 0) :
    biprod.map f₁ f₂ ≫ biprod.map π₁ π₂ = 0 := by
  apply biprod.hom_ext' <;> simp [biprod.inl_map_assoc, biprod.inr_map_assoc,
    reassoc_of% w₁, reassoc_of% w₂]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.biprod_map_map_condition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.biprod_map_map_condition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.biprod_map_map_condition ``Submission.DifferentialGeometry.Topology.SingularPair.biprod_map_map_condition

def isColimitBiprodCokernelCofork (w₁ : f₁ ≫ π₁ = 0) (w₂ : f₂ ≫ π₂ = 0)
    (h₁ : _root_.CategoryTheory.Limits.IsColimit (CokernelCofork.ofπ π₁ w₁)) (h₂ : _root_.CategoryTheory.Limits.IsColimit (CokernelCofork.ofπ π₂ w₂)) :
    IsColimit (CokernelCofork.ofπ (biprod.map π₁ π₂) (biprod_map_map_condition w₁ w₂)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} h hh ↦ biprod.desc
      (Cofork.IsColimit.desc h₁ (biprod.inl ≫ h) (by
        rw [_root_.CategoryTheory.Limits.zero_comp, ← biprod.inl_map_assoc, hh, _root_.CategoryTheory.Limits.comp_zero]))
      (Cofork.IsColimit.desc h₂ (biprod.inr ≫ h) (by
        rw [_root_.CategoryTheory.Limits.zero_comp, ← biprod.inr_map_assoc, hh, _root_.CategoryTheory.Limits.comp_zero])))
    (fun {W} h hh ↦ by
      apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, biprod.inl_desc]
        exact Cofork.IsColimit.π_desc' h₁ _ _
      · rw [biprod.inr_map_assoc, biprod.inr_desc]
        exact Cofork.IsColimit.π_desc' h₂ _ _)
    (fun {W} h hh m hm ↦ by
      apply biprod.hom_ext'
      · apply Cofork.IsColimit.hom_ext h₁
        rw [biprod.inl_desc, Cofork.IsColimit.π_desc', ← hm, Cofork.π_ofπ, biprod.inl_map_assoc]
      · apply Cofork.IsColimit.hom_ext h₂
        rw [biprod.inr_desc, Cofork.IsColimit.π_desc', ← hm, Cofork.π_ofπ, biprod.inr_map_assoc])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isColimitBiprodCokernelCofork then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isColimitBiprodCokernelCofork"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isColimitBiprodCokernelCofork ``Submission.DifferentialGeometry.Topology.SingularPair.isColimitBiprodCokernelCofork

end BiprodCofork

section Split

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C] (X : C)

@[reassoc]
lemma split_lift_desc :
    biprod.lift (𝟙 X) (-𝟙 X) ≫ biprod.desc (𝟙 X) (𝟙 X) = 0 := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.split_lift_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.split_lift_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.split_lift_desc ``Submission.DifferentialGeometry.Topology.SingularPair.split_lift_desc

def splitShortComplex : _root_.CategoryTheory.ShortComplex C :=
  ShortComplex.mk (biprod.lift (𝟙 X) (-𝟙 X)) (biprod.desc (𝟙 X) (𝟙 X)) (split_lift_desc X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex

@[simp] lemma splitShortComplex_X₁ : (splitShortComplex X).X₁ = X := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₁ ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₁
@[simp] lemma splitShortComplex_X₂ : (splitShortComplex X).X₂ = (X ⊞ X) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₂ ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₂
@[simp] lemma splitShortComplex_X₃ : (splitShortComplex X).X₃ = X := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₃ ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex_X₃
@[simp] lemma splitShortComplex_f : (splitShortComplex X).f = biprod.lift (𝟙 X) (-𝟙 X) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex_f ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex_f
@[simp] lemma splitShortComplex_g : (splitShortComplex X).g = biprod.desc (𝟙 X) (𝟙 X) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex_g then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex_g"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex_g ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex_g

lemma split_id :
    biprod.fst ≫ biprod.lift (𝟙 X) (-𝟙 X) + biprod.desc (𝟙 X) (𝟙 X) ≫ biprod.inr =
      𝟙 (X ⊞ X) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.split_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.split_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.split_id ``Submission.DifferentialGeometry.Topology.SingularPair.split_id

def splitShortComplexSplitting : (splitShortComplex X).Splitting where
  r := biprod.fst
  s := biprod.inr
  f_r := biprod.lift_fst _ _
  s_g := biprod.inr_desc _ _
  id := split_id X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplexSplitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplexSplitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplexSplitting ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplexSplitting

lemma splitShortComplex_shortExact [_root_.CategoryTheory.Limits.HasZeroObject C] : (splitShortComplex X).ShortExact :=
  (splitShortComplexSplitting X).shortExact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitShortComplex_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitShortComplex_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitShortComplex_shortExact ``Submission.DifferentialGeometry.Topology.SingularPair.splitShortComplex_shortExact

end Split

variable {K : SSet.{u}} (A B : K.Subcomplex)

def pairOfLE {A B : K.Subcomplex} (h : A ≤ B) : A.pair ⟶ B.pair :=
  (SSet.Subcomplex.toPairFunctor K).map (_root_.CategoryTheory.homOfLE h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairOfLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairOfLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairOfLE ``Submission.DifferentialGeometry.Topology.SingularPair.pairOfLE

@[simp]
lemma pairOfLE_left {A B : K.Subcomplex} (h : A ≤ B) :
    (pairOfLE h).left = SSet.Subcomplex.homOfLE h := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairOfLE_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairOfLE_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairOfLE_left ``Submission.DifferentialGeometry.Topology.SingularPair.pairOfLE_left

@[simp]
lemma pairOfLE_right {A B : K.Subcomplex} (h : A ≤ B) : (pairOfLE h).right = 𝟙 K := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairOfLE_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairOfLE_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairOfLE_right ``Submission.DifferentialGeometry.Topology.SingularPair.pairOfLE_right

lemma pairOfLE_comp {A B C : K.Subcomplex} (h : A ≤ B) (h' : B ≤ C) :
    pairOfLE h ≫ pairOfLE h' = pairOfLE (h.trans h') := by
  rw [pairOfLE, pairOfLE, ← Functor.map_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairOfLE_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairOfLE_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairOfLE_comp ``Submission.DifferentialGeometry.Topology.SingularPair.pairOfLE_comp

lemma pairOfLE_refl (A : K.Subcomplex) : pairOfLE (le_refl A) = 𝟙 A.pair :=
  (SSet.Subcomplex.toPairFunctor K).map_id A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairOfLE_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairOfLE_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairOfLE_refl ``Submission.DifferentialGeometry.Topology.SingularPair.pairOfLE_refl

variable (R : ModuleCat.{u} ℤ)

abbrev quotMap {A B : K.Subcomplex} (h : A ≤ B) :
    A.pair.chainComplex R ⟶ B.pair.chainComplex R :=
  SSetPair.chainComplexMap (pairOfLE h) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMap ``Submission.DifferentialGeometry.Topology.SingularPair.quotMap

lemma quotMap_comp {A B C : K.Subcomplex} (h : A ≤ B) (h' : B ≤ C) :
    quotMap R h ≫ quotMap R h' = quotMap R (h.trans h') := by
  rw [quotMap, quotMap, quotMap, ← Functor.map_comp, pairOfLE_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMap_comp ``Submission.DifferentialGeometry.Topology.SingularPair.quotMap_comp

lemma quotMap_refl (A : K.Subcomplex) : quotMap R (le_refl A) = 𝟙 _ := by
  rw [quotMap, pairOfLE_refl]
  exact CategoryTheory.Functor.map_id _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMap_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMap_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMap_refl ``Submission.DifferentialGeometry.Topology.SingularPair.quotMap_refl

lemma chainComplexMap_pairOfLE_right {A B : K.Subcomplex} (h : A ≤ B) :
    SSet.chainComplexMap (pairOfLE h).right R = 𝟙 (K.chainComplex R) :=
  CategoryTheory.Functor.map_id _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.chainComplexMap_pairOfLE_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.chainComplexMap_pairOfLE_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.chainComplexMap_pairOfLE_right ``Submission.DifferentialGeometry.Topology.SingularPair.chainComplexMap_pairOfLE_right

abbrev quotπ (A : K.Subcomplex) : K.chainComplex R ⟶ A.pair.chainComplex R :=
  A.pair.chainComplexπ R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotπ ``Submission.DifferentialGeometry.Topology.SingularPair.quotπ

abbrev subι (A : K.Subcomplex) : (A : SSet.{u}).chainComplex R ⟶ K.chainComplex R :=
  SSet.chainComplexMap A.ι R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.subι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.subι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.subι ``Submission.DifferentialGeometry.Topology.SingularPair.subι

instance mono_subι (A : K.Subcomplex) : _root_.CategoryTheory.Mono (subι R A) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap A.pair.hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mono_subι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mono_subι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mono_subι ``Submission.DifferentialGeometry.Topology.SingularPair.mono_subι

@[reassoc (attr := simp)]
lemma subι_quotπ (A : K.Subcomplex) : subι R A ≫ quotπ R A = 0 :=
  A.pair.chainComplex_condition R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.subι_quotπ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.subι_quotπ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.subι_quotπ ``Submission.DifferentialGeometry.Topology.SingularPair.subι_quotπ

@[reassoc (attr := simp)]
lemma quotπ_quotMap {A B : K.Subcomplex} (h : A ≤ B) :
    quotπ R A ≫ quotMap R h = quotπ R B := by
  have := (chainComplexMap_right_chainComplexπ R (pairOfLE h)).symm
  rw [chainComplexMap_pairOfLE_right] at this
  exact this.trans (Category.id_comp _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotπ_quotMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotπ_quotMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotπ_quotMap ``Submission.DifferentialGeometry.Topology.SingularPair.quotπ_quotMap

abbrev q₁ : (A ⊓ B).pair.chainComplex R ⟶ A.pair.chainComplex R :=
  quotMap R (inf_le_left : A ⊓ B ≤ A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.q₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.q₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.q₁ ``Submission.DifferentialGeometry.Topology.SingularPair.q₁

abbrev q₂ : (A ⊓ B).pair.chainComplex R ⟶ B.pair.chainComplex R :=
  quotMap R (inf_le_right : A ⊓ B ≤ B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.q₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.q₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.q₂ ``Submission.DifferentialGeometry.Topology.SingularPair.q₂

abbrev r₁ : A.pair.chainComplex R ⟶ (A ⊔ B).pair.chainComplex R :=
  quotMap R (le_sup_left : A ≤ A ⊔ B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.r₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.r₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.r₁ ``Submission.DifferentialGeometry.Topology.SingularPair.r₁

abbrev r₂ : B.pair.chainComplex R ⟶ (A ⊔ B).pair.chainComplex R :=
  quotMap R (le_sup_right : B ≤ A ⊔ B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.r₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.r₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.r₂ ``Submission.DifferentialGeometry.Topology.SingularPair.r₂

@[reassoc (attr := simp)]
lemma q₁_r₁ : q₁ A B R ≫ r₁ A B R = q₂ A B R ≫ r₂ A B R := by
  simp only [q₁, r₁, q₂, r₂, quotMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.q₁_r₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.q₁_r₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.q₁_r₁ ``Submission.DifferentialGeometry.Topology.SingularPair.q₁_r₁

@[reassoc]
lemma quot_lift_desc :
    biprod.lift (q₁ A B R) (-(q₂ A B R)) ≫ biprod.desc (r₁ A B R) (r₂ A B R) = 0 := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quot_lift_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quot_lift_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quot_lift_desc ``Submission.DifferentialGeometry.Topology.SingularPair.quot_lift_desc

def quotMV : _root_.CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (biprod.lift (q₁ A B R) (-(q₂ A B R))) (biprod.desc (r₁ A B R) (r₂ A B R))
    (quot_lift_desc A B R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV

@[simp] lemma quotMV_X₁ : (quotMV A B R).X₁ = (A ⊓ B).pair.chainComplex R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_X₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_X₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_X₁ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_X₁
@[simp] lemma quotMV_X₂ :
    (quotMV A B R).X₂ = (A.pair.chainComplex R ⊞ B.pair.chainComplex R) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_X₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_X₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_X₂ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_X₂
@[simp] lemma quotMV_X₃ : (quotMV A B R).X₃ = (A ⊔ B).pair.chainComplex R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_X₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_X₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_X₃ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_X₃
@[simp] lemma quotMV_f : (quotMV A B R).f = biprod.lift (q₁ A B R) (-(q₂ A B R)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_f ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_f
@[simp] lemma quotMV_g : (quotMV A B R).g = biprod.desc (r₁ A B R) (r₂ A B R) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_g then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_g"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_g ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_g

def mvToSplit : mvShortComplex A B R ⟶ splitShortComplex (K.chainComplex R) where
  τ₁ := subι R (A ⊓ B)
  τ₂ := biprod.map (subι R A) (subι R B)
  τ₃ := subι R (A ⊔ B)
  comm₁₂ := by
    dsimp only [mvShortComplex, splitShortComplex]
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  comm₂₃ := by
    dsimp only [mvShortComplex, splitShortComplex]
    apply biprod.hom_ext' <;> simp [← Functor.map_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvToSplit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvToSplit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvToSplit ``Submission.DifferentialGeometry.Topology.SingularPair.mvToSplit

def splitToQuotMV : splitShortComplex (K.chainComplex R) ⟶ quotMV A B R where
  τ₁ := quotπ R (A ⊓ B)
  τ₂ := biprod.map (quotπ R A) (quotπ R B)
  τ₃ := quotπ R (A ⊔ B)
  comm₁₂ := by
    dsimp only [splitShortComplex, quotMV]
    apply biprod.hom_ext <;> simp
  comm₂₃ := by
    dsimp only [splitShortComplex, quotMV]
    apply biprod.hom_ext' <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.splitToQuotMV then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.splitToQuotMV"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.splitToQuotMV ``Submission.DifferentialGeometry.Topology.SingularPair.splitToQuotMV

lemma mvToSplit_splitToQuotMV : mvToSplit A B R ≫ splitToQuotMV A B R = 0 := by
  refine ShortComplex.hom_ext _ _ ?_ ?_ ?_
  · exact subι_quotπ R (A ⊓ B)
  · exact biprod_map_map_condition (subι_quotπ R A) (subι_quotπ R B)
  · exact subι_quotπ R (A ⊔ B)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvToSplit_splitToQuotMV then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvToSplit_splitToQuotMV"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvToSplit_splitToQuotMV ``Submission.DifferentialGeometry.Topology.SingularPair.mvToSplit_splitToQuotMV

def quotMVSnakeInput : ShortComplex.SnakeInput (ChainComplex (ModuleCat.{u} ℤ) ℕ) where
  L₀ := ShortComplex.mk (0 : (0 : ChainComplex (ModuleCat.{u} ℤ) ℕ) ⟶ 0) 0 _root_.CategoryTheory.Limits.zero_comp
  L₁ := mvShortComplex A B R
  L₂ := splitShortComplex (K.chainComplex R)
  L₃ := quotMV A B R
  v₀₁ := 0
  v₁₂ := mvToSplit A B R
  v₂₃ := splitToQuotMV A B R
  w₀₂ := _root_.CategoryTheory.Limits.zero_comp
  w₁₃ := mvToSplit_splitToQuotMV A B R
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    · refine (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ ?_ (_root_.CategoryTheory.Limits.isZero_zero _))
      exact mono_subι R (A ⊓ B)
    · refine (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ ?_ (_root_.CategoryTheory.Limits.isZero_zero _))
      exact biprod.map_mono _ _
    · refine (KernelFork.isLimitMapConeEquiv _ _).symm
        (KernelFork.IsLimit.ofMonoOfIsZero _ ?_ (_root_.CategoryTheory.Limits.isZero_zero _))
      exact mono_subι R (A ⊔ B)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((A ⊓ B).pair.isColimitCokernelCoforkChainComplex R)
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (isColimitBiprodCokernelCofork (subι_quotπ R A) (subι_quotπ R B)
          (A.pair.isColimitCokernelCoforkChainComplex R)
          (B.pair.isColimitCokernelCoforkChainComplex R))
    · exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((A ⊔ B).pair.isColimitCokernelCoforkChainComplex R)
  L₁_exact := (mvShortComplex_shortExact A B R).exact
  epi_L₁_g := (mvShortComplex_shortExact A B R).epi_g
  L₂_exact := (splitShortComplex_shortExact _).exact
  mono_L₂_f := (splitShortComplex_shortExact _).mono_f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput

lemma quotMVSnakeInput_L₃ : (quotMVSnakeInput A B R).L₃ = quotMV A B R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_L₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_L₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_L₃ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_L₃

lemma quotMVSnakeInput_δ : (quotMVSnakeInput A B R).δ = 0 :=
  (_root_.CategoryTheory.Limits.isZero_zero _).eq_of_src _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_δ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_δ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_δ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVSnakeInput_δ

theorem quotMV_shortExact : (quotMV A B R).ShortExact where
  exact := (quotMVSnakeInput A B R).L₃_exact
  mono_f := (quotMVSnakeInput A B R).L₂'_exact.mono_g (quotMVSnakeInput_δ A B R)
  epi_g := by
    have : _root_.CategoryTheory.Epi (quotMVSnakeInput A B R).L₂.g := (splitShortComplex_shortExact _).epi_g
    exact (quotMVSnakeInput A B R).epi_L₃_g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_shortExact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_shortExact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_shortExact ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_shortExact

def quotMVδ (n : ℕ) :
    (A ⊔ B).pair.homology R (n + 1) ⟶ (A ⊓ B).pair.homology R n :=
  (quotMV_shortExact A B R).δ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVδ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVδ

@[reassoc (attr := simp)]
lemma quotMVδ_comp (n : ℕ) :
    quotMVδ A B R n ≫ _root_.HomologicalComplex.homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n = 0 :=
  (quotMV_shortExact A B R).δ_comp (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVδ_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVδ_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVδ_comp ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVδ_comp

@[reassoc (attr := simp)]
lemma comp_quotMVδ (n : ℕ) :
    homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) (n + 1) ≫ quotMVδ A B R n = 0 :=
  (quotMV_shortExact A B R).comp_δ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.comp_quotMVδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.comp_quotMVδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.comp_quotMVδ ``Submission.DifferentialGeometry.Topology.SingularPair.comp_quotMVδ

lemma homologyMap_quot_lift_desc (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n ≫
      homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) n = 0 := by
  rw [← _root_.HomologicalComplex.homologyMap_comp, quot_lift_desc, _root_.HomologicalComplex.homologyMap_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_desc ``Submission.DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_desc

theorem quotMV_exact₁ (n : ℕ) :
    (ShortComplex.mk (quotMVδ A B R n) (_root_.HomologicalComplex.homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n)
      (quotMVδ_comp A B R n)).Exact :=
  (quotMV_shortExact A B R).homology_exact₁ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_exact₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_exact₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_exact₁ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_exact₁

theorem quotMV_exact₂ (n : ℕ) :
    (ShortComplex.mk (_root_.HomologicalComplex.homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n)
      (_root_.HomologicalComplex.homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) n)
      (homologyMap_quot_lift_desc A B R n)).Exact :=
  (quotMV_shortExact A B R).homology_exact₂ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_exact₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_exact₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_exact₂ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_exact₂

theorem quotMV_exact₃ (n : ℕ) :
    (ShortComplex.mk (_root_.HomologicalComplex.homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) (n + 1)) (quotMVδ A B R n)
      (comp_quotMVδ A B R n)).Exact :=
  (quotMV_shortExact A B R).homology_exact₃ (n + 1) n rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_exact₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_exact₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_exact₃ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_exact₃

def homologyBiprodIsoOf (X Y : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    (X ⊞ Y).homology n ≅ (X.homology n ⊞ Y.homology n) where
  hom := biprod.lift (_root_.HomologicalComplex.homologyMap biprod.fst n) (_root_.HomologicalComplex.homologyMap biprod.snd n)
  inv := biprod.desc (_root_.HomologicalComplex.homologyMap biprod.inl n) (_root_.HomologicalComplex.homologyMap biprod.inr n)
  hom_inv_id := by
    rw [biprod.lift_desc, ← _root_.HomologicalComplex.homologyMap_comp, ← _root_.HomologicalComplex.homologyMap_comp, ← _root_.HomologicalComplex.homologyMap_add,
      biprod.total, _root_.HomologicalComplex.homologyMap_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp [← _root_.HomologicalComplex.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf ``Submission.DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf

abbrev quotHomologyMap {A B : K.Subcomplex} (h : A ≤ B) (n : ℕ) :
    A.pair.homology R n ⟶ B.pair.homology R n :=
  SSetPair.homologyMap (pairOfLE h) R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotHomologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.quotHomologyMap

lemma quotHomologyMap_comp {A B C : K.Subcomplex} (h : A ≤ B) (h' : B ≤ C) (n : ℕ) :
    quotHomologyMap R h n ≫ quotHomologyMap R h' n = quotHomologyMap R (h.trans h') n := by
  rw [quotHomologyMap, quotHomologyMap, quotHomologyMap, ← SSetPair.homologyMap_comp,
    pairOfLE_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotHomologyMap_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotHomologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotHomologyMap_comp ``Submission.DifferentialGeometry.Topology.SingularPair.quotHomologyMap_comp

lemma quotHomologyMap_refl (A : K.Subcomplex) (n : ℕ) :
    quotHomologyMap R (le_refl A) n = 𝟙 _ := by
  rw [quotHomologyMap, pairOfLE_refl, SSetPair.homologyMap_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotHomologyMap_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotHomologyMap_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotHomologyMap_refl ``Submission.DifferentialGeometry.Topology.SingularPair.quotHomologyMap_refl

@[reassoc (attr := simp)]
lemma homologyπ_quotHomologyMap {A B : K.Subcomplex} (h : A ≤ B) (n : ℕ) :
    A.pair.homologyπ R n ≫ quotHomologyMap R h n = B.pair.homologyπ R n := by
  rw [quotHomologyMap, SSetPair.homologyMap, SSetPair.homologyπ, ← _root_.HomologicalComplex.homologyMap_comp]
  exact congrArg (fun φ ↦ _root_.HomologicalComplex.homologyMap φ n) (quotπ_quotMap R h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyπ_quotHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyπ_quotHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyπ_quotHomologyMap ``Submission.DifferentialGeometry.Topology.SingularPair.homologyπ_quotHomologyMap

def quotMVLift (n : ℕ) :
    (A ⊓ B).pair.homology R n ⟶ (A.pair.homology R n ⊞ B.pair.homology R n) :=
  biprod.lift (quotHomologyMap R (inf_le_left : A ⊓ B ≤ A) n)
    (-(quotHomologyMap R (inf_le_right : A ⊓ B ≤ B) n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVLift ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVLift

def quotMVDesc (n : ℕ) :
    (A.pair.homology R n ⊞ B.pair.homology R n) ⟶ (A ⊔ B).pair.homology R n :=
  biprod.desc (quotHomologyMap R (le_sup_left : A ≤ A ⊔ B) n)
    (quotHomologyMap R (le_sup_right : B ≤ A ⊔ B) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVDesc ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVDesc

@[simp]
lemma quotMVLift_fst (n : ℕ) :
    quotMVLift A B R n ≫ biprod.fst = quotHomologyMap R (inf_le_left : A ⊓ B ≤ A) n :=
  biprod.lift_fst _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVLift_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVLift_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVLift_fst ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVLift_fst

@[simp]
lemma quotMVLift_snd (n : ℕ) :
    quotMVLift A B R n ≫ biprod.snd = -quotHomologyMap R (inf_le_right : A ⊓ B ≤ B) n :=
  biprod.lift_snd _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVLift_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVLift_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVLift_snd ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVLift_snd

@[simp]
lemma inl_quotMVDesc (n : ℕ) :
    biprod.inl ≫ quotMVDesc A B R n = quotHomologyMap R (le_sup_left : A ≤ A ⊔ B) n :=
  biprod.inl_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inl_quotMVDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inl_quotMVDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inl_quotMVDesc ``Submission.DifferentialGeometry.Topology.SingularPair.inl_quotMVDesc

@[simp]
lemma inr_quotMVDesc (n : ℕ) :
    biprod.inr ≫ quotMVDesc A B R n = quotHomologyMap R (le_sup_right : B ≤ A ⊔ B) n :=
  biprod.inr_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inr_quotMVDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inr_quotMVDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inr_quotMVDesc ``Submission.DifferentialGeometry.Topology.SingularPair.inr_quotMVDesc

lemma homologyMap_quot_lift_homologyBiprodIsoOf_hom (n : ℕ) :
    _root_.HomologicalComplex.homologyMap (biprod.lift (q₁ A B R) (-(q₂ A B R))) n ≫
      (homologyBiprodIsoOf _ _ n).hom = quotMVLift A B R n := by
  dsimp only [homologyBiprodIsoOf, quotMVLift]
  apply biprod.hom_ext
  · simp [← _root_.HomologicalComplex.homologyMap_comp]
  · simp [← _root_.HomologicalComplex.homologyMap_comp, _root_.HomologicalComplex.homologyMap_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_homologyBiprodIsoOf_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_homologyBiprodIsoOf_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_homologyBiprodIsoOf_hom ``Submission.DifferentialGeometry.Topology.SingularPair.homologyMap_quot_lift_homologyBiprodIsoOf_hom

lemma homologyBiprodIsoOf_inv_homologyMap_quot_desc (n : ℕ) :
    (homologyBiprodIsoOf _ _ n).inv ≫ _root_.HomologicalComplex.homologyMap (biprod.desc (r₁ A B R) (r₂ A B R)) n =
      quotMVDesc A B R n := by
  dsimp only [homologyBiprodIsoOf, quotMVDesc]
  apply biprod.hom_ext'
  · simp [← _root_.HomologicalComplex.homologyMap_comp]
  · simp [← _root_.HomologicalComplex.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf_inv_homologyMap_quot_desc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf_inv_homologyMap_quot_desc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf_inv_homologyMap_quot_desc ``Submission.DifferentialGeometry.Topology.SingularPair.homologyBiprodIsoOf_inv_homologyMap_quot_desc

@[reassoc (attr := simp)]
lemma quotMVδ_quotMVLift (n : ℕ) : quotMVδ A B R n ≫ quotMVLift A B R n = 0 := by
  rw [← homologyMap_quot_lift_homologyBiprodIsoOf_hom, quotMVδ_comp_assoc, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVδ_quotMVLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVδ_quotMVLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVδ_quotMVLift ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVδ_quotMVLift

@[reassoc (attr := simp)]
lemma quotMVLift_quotMVDesc (n : ℕ) : quotMVLift A B R n ≫ quotMVDesc A B R n = 0 := by
  rw [← homologyMap_quot_lift_homologyBiprodIsoOf_hom,
    ← homologyBiprodIsoOf_inv_homologyMap_quot_desc, Category.assoc, Iso.hom_inv_id_assoc,
    homologyMap_quot_lift_desc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVLift_quotMVDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVLift_quotMVDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVLift_quotMVDesc ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVLift_quotMVDesc

@[reassoc (attr := simp)]
lemma quotMVDesc_quotMVδ (n : ℕ) : quotMVDesc A B R (n + 1) ≫ quotMVδ A B R n = 0 := by
  rw [← homologyBiprodIsoOf_inv_homologyMap_quot_desc, Category.assoc, comp_quotMVδ, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMVDesc_quotMVδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMVDesc_quotMVδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMVDesc_quotMVδ ``Submission.DifferentialGeometry.Topology.SingularPair.quotMVDesc_quotMVδ

theorem quotMV_exact₁' (n : ℕ) :
    (ShortComplex.mk (quotMVδ A B R n) (quotMVLift A B R n)
      (quotMVδ_quotMVLift A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₁ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (homologyBiprodIsoOf _ _ n)
    (by simp) (by simp [homologyMap_quot_lift_homologyBiprodIsoOf_hom])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_exact₁' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_exact₁'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_exact₁' ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_exact₁'

theorem quotMV_exact₂' (n : ℕ) :
    (ShortComplex.mk (quotMVLift A B R n) (quotMVDesc A B R n)
      (quotMVLift_quotMVDesc A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₂ A B R n)
  exact ShortComplex.isoMk (Iso.refl _) (homologyBiprodIsoOf _ _ n) (Iso.refl _)
    (by simp [homologyMap_quot_lift_homologyBiprodIsoOf_hom])
    (by simp [← homologyBiprodIsoOf_inv_homologyMap_quot_desc])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_exact₂' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_exact₂'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_exact₂' ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_exact₂'

theorem quotMV_exact₃' (n : ℕ) :
    (ShortComplex.mk (quotMVDesc A B R (n + 1)) (quotMVδ A B R n)
      (quotMVDesc_quotMVδ A B R n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (quotMV_exact₃ A B R n)
  exact ShortComplex.isoMk (homologyBiprodIsoOf _ _ (n + 1)) (Iso.refl _) (Iso.refl _)
    (by simp [← homologyBiprodIsoOf_inv_homologyMap_quot_desc]) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quotMV_exact₃' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quotMV_exact₃'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quotMV_exact₃' ``Submission.DifferentialGeometry.Topology.SingularPair.quotMV_exact₃'

end DifferentialGeometry.Topology.SingularPair
