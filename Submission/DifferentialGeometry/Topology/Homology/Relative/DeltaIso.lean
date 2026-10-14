import Submission.DifferentialGeometry.Topology.Homology.Spheres.SphereHomology
import Submission.DifferentialGeometry.Topology.Homology.Relative.PairVanishing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

theorem isIso_δ_of_isZero (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X (i + 2))) (h₂ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X (i + 1))) :
    IsIso (δ R X A (i + 1)) := by
  have hmono : _root_.CategoryTheory.Mono (δ R X A (i + 1)) :=
    (les_exact₃ R X A (i + 1)).mono_g_iff.2 (h₁.eq_zero_of_src _)
  have hepi : _root_.CategoryTheory.Epi (δ R X A (i + 1)) :=
    (les_exact₁ R X A (i + 1)).epi_f_iff.2 (h₂.eq_zero_of_tgt _)
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_δ_of_isZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_δ_of_isZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_δ_of_isZero ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_δ_of_isZero

theorem isIso_δred_of_isZero (X : TopCat.{u}) (A : Set X)
    (h₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X 1)) (h₂ : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R X)) : _root_.CategoryTheory.IsIso (δred R X A) := by
  have hmono : _root_.CategoryTheory.Mono (δred R X A) :=
    (les_red_exact₃ R X A).mono_g_iff.2 (h₁.eq_zero_of_src _)
  have hepi : _root_.CategoryTheory.Epi (δred R X A) :=
    (les_red_exact₁ R X A).epi_f_iff.2 (h₂.eq_zero_of_tgt _)
  exact _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_δred_of_isZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_δred_of_isZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_δred_of_isZero ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_δred_of_isZero

def δIsoOfIsZero (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X (i + 2))) (h₂ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X (i + 1))) :
    relativeHomology R X A (i + 2) ≅ singularHomology R (TopCat.of A) (i + 1) :=
  have := isIso_δ_of_isZero R X A i h₁ h₂
  _root_.CategoryTheory.asIso (δ R X A (i + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero ``Submission.DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero

lemma δIsoOfIsZero_hom (X : TopCat.{u}) (A : Set X) (i : ℕ)
    (h₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X (i + 2))) (h₂ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X (i + 1))) :
    (δIsoOfIsZero R X A i h₁ h₂).hom = δ R X A (i + 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero_hom ``Submission.DifferentialGeometry.Topology.SingularPair.δIsoOfIsZero_hom

def δredIsoOfIsZero (X : TopCat.{u}) (A : Set X)
    (h₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X 1)) (h₂ : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R X)) :
    relativeHomology R X A 1 ≅ reducedHomologyZero R (TopCat.of A) :=
  have := isIso_δred_of_isZero R X A h₁ h₂
  _root_.CategoryTheory.asIso (δred R X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero ``Submission.DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero

lemma δredIsoOfIsZero_hom (X : TopCat.{u}) (A : Set X)
    (h₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R X 1)) (h₂ : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R X)) :
    (δredIsoOfIsZero R X A h₁ h₂).hom = δred R X A := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero_hom ``Submission.DifferentialGeometry.Topology.SingularPair.δredIsoOfIsZero_hom

theorem δred_natural {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) :
    δred R X A ≫ reducedHomologyZeroMap R (restr f hf) = relativeHomologyMap R f hf 1 ≫ δred R Y B := by
  rw [← _root_.CategoryTheory.cancel_mono (reducedHomologyZeroInclusion R (TopCat.of B)), Category.assoc, Category.assoc, reducedHomologyZeroMap_ι,
    δred_ι, δred_ι_assoc]
  exact δ_natural R f hf 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.δred_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.δred_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.δred_natural ``Submission.DifferentialGeometry.Topology.SingularPair.δred_natural

theorem isZero_relativeHomology_zero_of_epi (X : TopCat.{u}) (A : Set X) (h : _root_.CategoryTheory.Epi (inclMap R X A 0)) :
    IsZero (relativeHomology R X A 0) := by
  have hπ : relπ R X A 0 = 0 := (les_exact₂ R X A 0).epi_f_iff.1 h
  have : _root_.CategoryTheory.Epi (relπ R X A 0) := inferInstanceAs (_root_.CategoryTheory.Epi ((pair X A).homologyπ R 0))
  exact IsZero.of_epi_eq_zero _ hπ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_epi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_epi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_epi ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_epi

theorem epi_inclMap_zero_of_pathConnected (X : TopCat.{u}) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] : _root_.CategoryTheory.Epi (inclMap R X A 0) := by
  have hε : _root_.CategoryTheory.IsIso (ε R X) := isIso_ε_of_pathConnected R X
  have hA : Nonempty (TopCat.of A) := inferInstanceAs (Nonempty A)
  have h : inclMap R X A 0 = ε R (TopCat.of A) ≫ _root_.CategoryTheory.inv (ε R X) := by
    rw [← inclMap_ε, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  have : _root_.CategoryTheory.Epi (ε R (TopCat.of A)) :=
    IsSplitEpi.epi _ (hf := ⟨⟨⟨εSection R (TopCat.of A), εSection_ε R (TopCat.of A)⟩⟩⟩)
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.epi_inclMap_zero_of_pathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.epi_inclMap_zero_of_pathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.epi_inclMap_zero_of_pathConnected ``Submission.DifferentialGeometry.Topology.SingularPair.epi_inclMap_zero_of_pathConnected

theorem isZero_relativeHomology_zero_of_pathConnected (X : TopCat.{u}) (A : Set X) [PathConnectedSpace X]
    [Nonempty A] : _root_.CategoryTheory.Limits.IsZero (relativeHomology R X A 0) :=
  isZero_relativeHomology_zero_of_epi R X A (epi_inclMap_zero_of_pathConnected R X A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_pathConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_pathConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_pathConnected ``Submission.DifferentialGeometry.Topology.SingularPair.isZero_relativeHomology_zero_of_pathConnected

lemma relativeHomologyMap_congr {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf hf' : Set.MapsTo f A B) (n : ℕ) : relativeHomologyMap R f hf n = relativeHomologyMap R f hf' n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_congr ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_congr

lemma relativeHomologyMap_eq_of_eq {X Y : TopCat.{u}} {A : Set X} {B : Set Y} {f g : X ⟶ Y} (h : f = g)
    (hf : Set.MapsTo f A B) (n : ℕ) : relativeHomologyMap R f hf n = relativeHomologyMap R g (h ▸ hf) n := by
  subst h; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_eq_of_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_eq_of_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_eq_of_eq ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_eq_of_eq

lemma mapsTo_id_of_subset {X : TopCat.{u}} {A A' : Set X} (h : A ⊆ A') :
    Set.MapsTo (𝟙 X) A A' := fun x hx => by simpa using h hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mapsTo_id_of_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mapsTo_id_of_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mapsTo_id_of_subset ``Submission.DifferentialGeometry.Topology.SingularPair.mapsTo_id_of_subset

lemma mapsTo_comp {X Y W : TopCat.{u}} {A : Set X} {B : Set Y} {D : Set W} {f : X ⟶ Y}
    {g : Y ⟶ W} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B D) : Set.MapsTo (f ≫ g) A D :=
  fun x hx => by simpa using hg (hf hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mapsTo_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mapsTo_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mapsTo_comp ``Submission.DifferentialGeometry.Topology.SingularPair.mapsTo_comp

lemma relativeHomologyMap_comp_id {X Y : TopCat.{u}} {A A' : Set X} {B B' : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f A' B') (hA : Set.MapsTo (𝟙 X) A A')
    (hB : Set.MapsTo (𝟙 Y) B B') (n : ℕ) :
    relativeHomologyMap R f hf n ≫ relativeHomologyMap R (𝟙 Y) hB n = relativeHomologyMap R (𝟙 X) hA n ≫ relativeHomologyMap R f hf' n := by
  rw [← relativeHomologyMap_comp R f (𝟙 Y) hf hB (mapsTo_comp hf hB) n,
    ← relativeHomologyMap_comp R (𝟙 X) f hA hf' (mapsTo_comp hA hf') n]
  exact relativeHomologyMap_eq_of_eq R (by simp) _ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp_id ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyMap_comp_id

def relativeHomologyIsoOfEq (X : TopCat.{u}) {A A' : Set X} (h : A = A') (n : ℕ) :
    relativeHomology R X A n ≅ relativeHomology R X A' n where
  hom := relativeHomologyMap R (𝟙 X) (mapsTo_id_of_subset h.le) n
  inv := relativeHomologyMap R (𝟙 X) (mapsTo_id_of_subset h.ge) n
  hom_inv_id := by
    subst h
    rw [relativeHomologyMap_id, Category.id_comp]
  inv_hom_id := by
    subst h
    rw [relativeHomologyMap_id, Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfEq ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfEq

section homeomorph

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y)

abbrev homeoHom : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom (f : C(X, Y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homeoHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homeoHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homeoHom ``Submission.DifferentialGeometry.Topology.SingularPair.homeoHom

lemma homeoHom_eq_toHomotopyEquiv : homeoHom f = TopCat.ofHom f.toHomotopyEquiv.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homeoHom_eq_toHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homeoHom_eq_toHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homeoHom_eq_toHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.homeoHom_eq_toHomotopyEquiv

@[simp]
lemma homeoHom_apply (x : X) : homeoHom f x = f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homeoHom_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homeoHom_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homeoHom_apply ``Submission.DifferentialGeometry.Topology.SingularPair.homeoHom_apply

lemma homeoHom_comp_symm : homeoHom f ≫ homeoHom f.symm = 𝟙 _ := by
  ext x
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homeoHom_comp_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homeoHom_comp_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homeoHom_comp_symm ``Submission.DifferentialGeometry.Topology.SingularPair.homeoHom_comp_symm

lemma symm_comp_homeoHom : homeoHom f.symm ≫ homeoHom f = 𝟙 _ := by
  ext x
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.symm_comp_homeoHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.symm_comp_homeoHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.symm_comp_homeoHom ``Submission.DifferentialGeometry.Topology.SingularPair.symm_comp_homeoHom

lemma mapsTo_homeoHom {A : Set X} {B : Set Y} (h : f '' A = B) :
    Set.MapsTo (homeoHom f) A B := by
  subst h
  exact Set.mapsTo_image f A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom ``Submission.DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom

lemma mapsTo_homeoHom_symm {A : Set X} {B : Set Y} (h : f '' A = B) :
    Set.MapsTo (homeoHom f.symm) B A := by
  subst h
  rintro _ ⟨a, ha, rfl⟩
  simpa using ha

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom_symm ``Submission.DifferentialGeometry.Topology.SingularPair.mapsTo_homeoHom_symm

def relativeHomologyIsoOfHomeomorphImage {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    relativeHomology R (TopCat.of X) A k ≅ relativeHomology R (TopCat.of Y) B k where
  hom := relativeHomologyMap R (homeoHom f) (mapsTo_homeoHom f h) k
  inv := relativeHomologyMap R (homeoHom f.symm) (mapsTo_homeoHom_symm f h) k
  hom_inv_id := by
    rw [← relativeHomologyMap_comp R _ _ _ _
      (mapsTo_comp (mapsTo_homeoHom f h) (mapsTo_homeoHom_symm f h)) k]
    exact (relativeHomologyMap_eq_of_eq R (homeoHom_comp_symm f) _ k).trans (relativeHomologyMap_id R _ _ _ k)
  inv_hom_id := by
    rw [← relativeHomologyMap_comp R _ _ _ _
      (mapsTo_comp (mapsTo_homeoHom_symm f h) (mapsTo_homeoHom f h)) k]
    exact (relativeHomologyMap_eq_of_eq R (symm_comp_homeoHom f) _ k).trans (relativeHomologyMap_id R _ _ _ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage

lemma relativeHomologyIsoOfHomeomorphImage_hom {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphImage R f h k).hom = relativeHomologyMap R (homeoHom f) (mapsTo_homeoHom f h) k :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_hom ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_hom

lemma relativeHomologyIsoOfHomeomorphImage_inv {A : Set X} {B : Set Y} (h : f '' A = B) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphImage R f h k).inv =
      relativeHomologyMap R (homeoHom f.symm) (mapsTo_homeoHom_symm f h) k :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_inv ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_inv

theorem isIso_relativeHomologyMap_homeoHom {A : Set X} {B : Set Y} (h : f '' A = B)
    (hf : Set.MapsTo (homeoHom f) A B) (k : ℕ) : _root_.CategoryTheory.IsIso (relativeHomologyMap R (homeoHom f) hf k) :=
  ⟨(relativeHomologyIsoOfHomeomorphImage R f h k).inv, (relativeHomologyIsoOfHomeomorphImage R f h k).hom_inv_id,
    (relativeHomologyIsoOfHomeomorphImage R f h k).inv_hom_id⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_relativeHomologyMap_homeoHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_relativeHomologyMap_homeoHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_relativeHomologyMap_homeoHom ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_relativeHomologyMap_homeoHom

def relativeHomologyIsoOfHomeomorph (A : Set X) (k : ℕ) :
    relativeHomology R (TopCat.of X) A k ≅ relativeHomology R (TopCat.of Y) (f '' A) k :=
  relativeHomologyIsoOfHomeomorphImage R f rfl k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph

lemma relativeHomologyIsoOfHomeomorph_hom (A : Set X) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorph R f A k).hom = relativeHomologyMap R (homeoHom f) (Set.mapsTo_image f A) k :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph_hom ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorph_hom

lemma homeomorph_image_eq_of_mem_iff {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) :
    f '' A = B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨f.symm y, (h _).2 (by simpa using hy), by simp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homeomorph_image_eq_of_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homeomorph_image_eq_of_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homeomorph_image_eq_of_mem_iff ``Submission.DifferentialGeometry.Topology.SingularPair.homeomorph_image_eq_of_mem_iff

def relativeHomologyIsoOfHomeomorphMemIff {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) (k : ℕ) :
    relativeHomology R (TopCat.of X) A k ≅ relativeHomology R (TopCat.of Y) B k :=
  relativeHomologyIsoOfHomeomorphImage R f (homeomorph_image_eq_of_mem_iff f h) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff

lemma relativeHomologyIsoOfHomeomorphMemIff_hom {A : Set X} {B : Set Y} (h : ∀ x, x ∈ A ↔ f x ∈ B) (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphMemIff R f h k).hom =
      relativeHomologyMap R (homeoHom f) (fun x hx => (h x).1 hx) k :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff_hom ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphMemIff_hom

lemma relativeHomologyIsoOfHomeomorphImage_natural {A A' : Set X} {B B' : Set Y} (h : f '' A = B)
    (h' : f '' A' = B') (hA : Set.MapsTo (𝟙 (TopCat.of X)) A A')
    (hB : Set.MapsTo (𝟙 (TopCat.of Y)) B B') (k : ℕ) :
    (relativeHomologyIsoOfHomeomorphImage R f h k).hom ≫ relativeHomologyMap R (𝟙 _) hB k =
      relativeHomologyMap R (𝟙 _) hA k ≫ (relativeHomologyIsoOfHomeomorphImage R f h' k).hom :=
  relativeHomologyMap_comp_id R _ _ _ hA hB k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_natural ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfHomeomorphImage_natural

end homeomorph

section nested

variable {X : Type u} [TopologicalSpace X]

lemma homeomorphPreimageVal_image {B B' : Set X} (h : B ⊆ B') (A : Set X) :
    homeomorphPreimageVal h '' (Subtype.val ⁻¹' (Subtype.val ⁻¹' A)) =
      (Subtype.val ⁻¹' A : Set B) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨⟨y, hy⟩, hy'⟩, hyA, hxy⟩
    cases hxy
    exact hyA
  · intro hxA
    exact ⟨⟨⟨x, h hx⟩, hx⟩, hxA, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.homeomorphPreimageVal_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.homeomorphPreimageVal_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.homeomorphPreimageVal_image ``Submission.DifferentialGeometry.Topology.SingularPair.homeomorphPreimageVal_image

def relativeHomologyIsoOfSubtypeSubtype {B B' : Set X} (h : B ⊆ B') (A : Set X) (k : ℕ) :
    relativeHomology R (TopCat.of (Subtype.val ⁻¹' B : Set B')) (Subtype.val ⁻¹' (Subtype.val ⁻¹' A)) k ≅
      relativeHomology R (TopCat.of B) (Subtype.val ⁻¹' A) k :=
  relativeHomologyIsoOfHomeomorphImage R (homeomorphPreimageVal h) (homeomorphPreimageVal_image h A) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfSubtypeSubtype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfSubtypeSubtype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfSubtypeSubtype ``Submission.DifferentialGeometry.Topology.SingularPair.relativeHomologyIsoOfSubtypeSubtype

end nested

end DifferentialGeometry.Topology.SingularPair

end
