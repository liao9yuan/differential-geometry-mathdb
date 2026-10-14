import Submission.DifferentialGeometry.Topology.Homology.SingularSubcomplex
import Submission.DifferentialGeometry.Topology.Homology.MayerVietoris.ShortExact
import Submission.DifferentialGeometry.Topology.Homology.Subdivision.SmallSimplices

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.HomologicalComplex _root_.Submission.HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ) (X : TopCat.{u}) (U V : Set X)

abbrev coverFam : Bool → Set X := fun b ↦ bif b then U else V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.coverFam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.coverFam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.coverFam ``Submission.DifferentialGeometry.Topology.SingularPair.coverFam

lemma small_coverFam : small X (coverFam X U V) = singSub X U ⊔ singSub X V :=
  small_pair U V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.small_coverFam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.small_coverFam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.small_coverFam ``Submission.DifferentialGeometry.Topology.SingularPair.small_coverFam

variable {X U V} in
lemma iUnion_interior_coverFam (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) :
    ⋃ b, interior (coverFam X U V b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ U ∪ V := hUV ▸ Set.mem_univ x
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · exact ⟨true, by simpa [coverFam, hU.interior_eq] using hx⟩
  · exact ⟨false, by simpa [coverFam, hV.interior_eq] using hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam ``Submission.DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam

variable {X U V} in
theorem isIso_homologyMap_sup_ι (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) : _root_.CategoryTheory.IsIso (SSet.homologyMap (singSub X U ⊔ singSub X V).ι R n) := by
  rw [← small_coverFam]
  exact isIso_homologyMap_small R _ (iUnion_interior_coverFam hU hV hUV) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_sup_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_sup_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_sup_ι ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_sup_ι

variable {X U V} in
def supIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    ((singSub X U ⊔ singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      singularHomology R X n :=
  @_root_.CategoryTheory.asIso _ _ _ _ _ (isIso_homologyMap_sup_ι R hU hV hUV n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.supIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.supIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.supIso ``Submission.DifferentialGeometry.Topology.SingularPair.supIso

variable {X U V} in
lemma supIso_hom (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (supIso R hU hV hUV n).hom = SSet.homologyMap (singSub X U ⊔ singSub X V).ι R n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.supIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.supIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.supIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.supIso_hom

def infIso (n : ℕ) :
    ((singSub X U ⊓ singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ≅
      singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  (SSet.homologyFunctor.{u} R n).mapIso (SSet.Subcomplex.eqToIso (singSub_inf X U V).symm) ≪≫
    singularSubcomplexHomologyIso X R (U ∩ V) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.infIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.infIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.infIso ``Submission.DifferentialGeometry.Topology.SingularPair.infIso

lemma infIso_hom (n : ℕ) :
    (infIso R X U V n).hom =
      SSet.homologyMap (SSet.Subcomplex.homOfLE (singSub_inf X U V).symm.le) R n ≫
        (singularSubcomplexHomologyIso X R (U ∩ V) n).hom := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.infIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.infIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.infIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.infIso_hom

def mvOpenLift (n : ℕ) :
    singularHomology R (TopCat.of (U ∩ V : Set X)) n ⟶ singularHomology R (TopCat.of U) n ⊞ singularHomology R (TopCat.of V) n :=
  biprod.lift (_root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) n)
    (-(_root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenLift ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenLift

def mvOpenDesc (n : ℕ) : singularHomology R (TopCat.of U) n ⊞ singularHomology R (TopCat.of V) n ⟶ singularHomology R X n :=
  biprod.desc (inclMap R X U n) (inclMap R X V n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenDesc ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenDesc

@[simp]
lemma mvOpenLift_fst (n : ℕ) :
    mvOpenLift R X U V n ≫ biprod.fst =
      homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_left : U ∩ V ⊆ U))) n :=
  biprod.lift_fst _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenLift_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenLift_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenLift_fst ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenLift_fst

@[simp]
lemma mvOpenLift_snd (n : ℕ) :
    mvOpenLift R X U V n ≫ biprod.snd =
      -_root_.HomologicalComplex.homologyMap ((singularChainFunctor R).map (inclOfLE (Set.inter_subset_right : U ∩ V ⊆ V))) n :=
  biprod.lift_snd _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenLift_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenLift_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenLift_snd ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenLift_snd

@[simp]
lemma inl_mvOpenDesc (n : ℕ) : biprod.inl ≫ mvOpenDesc R X U V n = inclMap R X U n :=
  biprod.inl_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inl_mvOpenDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inl_mvOpenDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inl_mvOpenDesc ``Submission.DifferentialGeometry.Topology.SingularPair.inl_mvOpenDesc

@[simp]
lemma inr_mvOpenDesc (n : ℕ) : biprod.inr ≫ mvOpenDesc R X U V n = inclMap R X V n :=
  biprod.inr_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inr_mvOpenDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inr_mvOpenDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inr_mvOpenDesc ``Submission.DifferentialGeometry.Topology.SingularPair.inr_mvOpenDesc

variable {X U V} in
def mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    singularHomology R X (n + 1) ⟶ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  (supIso R hU hV hUV (n + 1)).inv ≫ mvδ (singSub X U) (singSub X V) R n ≫
    (infIso R X U V n).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδ ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδ

abbrev biprodHIso (n : ℕ) :
    (((singSub X U : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n ⊞
      ((singSub X V : (TopCat.toSSet.obj X).Subcomplex) : SSet.{u}).homology R n) ≅
      (singularHomology R (TopCat.of U) n ⊞ singularHomology R (TopCat.of V) n) :=
  biprod.mapIso (singularSubcomplexHomologyIso X R U n) (singularSubcomplexHomologyIso X R V n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.biprodHIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.biprodHIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.biprodHIso ``Submission.DifferentialGeometry.Topology.SingularPair.biprodHIso

lemma infIso_hom_mvOpenLift (n : ℕ) :
    (infIso R X U V n).hom ≫ mvOpenLift R X U V n =
      mvLift (singSub X U) (singSub X V) R n ≫ (biprodHIso R X U V n).hom := by
  have h1 : (singularSubcomplexHomologyIso X R (U ∩ V) n).hom ≫ (mvOpenLift R X U V n ≫ biprod.fst) =
      SSet.homologyMap (SSet.Subcomplex.homOfLE
        (singSub_mono X (Set.inter_subset_left : U ∩ V ⊆ U))) R n ≫ (singularSubcomplexHomologyIso X R U n).hom := by
    rw [mvOpenLift_fst]
    exact singularSubcomplexHomologyIso_hom_map_inclOfLE R _ n
  have h2 : (singularSubcomplexHomologyIso X R (U ∩ V) n).hom ≫ (mvOpenLift R X U V n ≫ biprod.snd) =
      -(SSet.homologyMap (SSet.Subcomplex.homOfLE
        (singSub_mono X (Set.inter_subset_right : U ∩ V ⊆ V))) R n ≫ (singularSubcomplexHomologyIso X R V n).hom) := by
    rw [mvOpenLift_snd]
    exact (Preadditive.comp_neg _ _).trans (congrArg Neg.neg (singularSubcomplexHomologyIso_hom_map_inclOfLE R _ n))
  apply biprod.hom_ext
  · rw [Category.assoc, infIso_hom, Category.assoc, h1, biprod.mapIso_hom, Category.assoc,
      biprod.map_fst, reassoc_of% (mvLift_fst (singSub X U) (singSub X V) R n),
      ← Category.assoc, ← SSet.homologyMap_comp]
    rfl
  · rw [Category.assoc, infIso_hom, Category.assoc, h2, biprod.mapIso_hom, Category.assoc,
      biprod.map_snd, reassoc_of% (mvLift_snd (singSub X U) (singSub X V) R n),
      Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc, ← SSet.homologyMap_comp]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.infIso_hom_mvOpenLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.infIso_hom_mvOpenLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.infIso_hom_mvOpenLift ``Submission.DifferentialGeometry.Topology.SingularPair.infIso_hom_mvOpenLift

lemma biprodHIso_hom_mvOpenDesc (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (biprodHIso R X U V n).hom ≫ mvOpenDesc R X U V n =
      mvDesc (singSub X U) (singSub X V) R n ≫ (supIso R hU hV hUV n).hom := by
  apply biprod.hom_ext'
  · rw [biprod.mapIso_hom, biprod.inl_map_assoc, inl_mvOpenDesc, singularSubcomplexHomologyIso_hom_inclMap,
      ← Category.assoc, inl_mvDesc, supIso_hom]
    erw [← SSet.homologyMap_comp]
    rw [SSet.Subcomplex.homOfLE_ι]
  · rw [biprod.mapIso_hom, biprod.inr_map_assoc, inr_mvOpenDesc, singularSubcomplexHomologyIso_hom_inclMap,
      ← Category.assoc, inr_mvDesc, supIso_hom]
    erw [← SSet.homologyMap_comp]
    rw [SSet.Subcomplex.homOfLE_ι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.biprodHIso_hom_mvOpenDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.biprodHIso_hom_mvOpenDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.biprodHIso_hom_mvOpenDesc ``Submission.DifferentialGeometry.Topology.SingularPair.biprodHIso_hom_mvOpenDesc

variable {X U V} in
lemma supIso_hom_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (supIso R hU hV hUV (n + 1)).hom ≫ mvOpenδ R hU hV hUV n =
      mvδ (singSub X U) (singSub X V) R n ≫ (infIso R X U V n).hom := by
  rw [mvOpenδ, Iso.hom_inv_id_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.supIso_hom_mvOpenδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.supIso_hom_mvOpenδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.supIso_hom_mvOpenδ ``Submission.DifferentialGeometry.Topology.SingularPair.supIso_hom_mvOpenδ

variable {X U V}

@[reassoc (attr := simp)]
lemma mvOpenδ_mvOpenLift (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    mvOpenδ R hU hV hUV n ≫ mvOpenLift R X U V n = 0 := by
  rw [mvOpenδ, Category.assoc, Category.assoc, infIso_hom_mvOpenLift, mvδ_mvLift_assoc,
    _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδ_mvOpenLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδ_mvOpenLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδ_mvOpenLift ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδ_mvOpenLift

@[reassoc (attr := simp)]
lemma mvOpenLift_mvOpenDesc (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    mvOpenLift R X U V n ≫ mvOpenDesc R X U V n = 0 := by
  rw [← _root_.CategoryTheory.cancel_epi (infIso R X U V n).hom, ← Category.assoc, infIso_hom_mvOpenLift,
    Category.assoc, biprodHIso_hom_mvOpenDesc R X U V hU hV hUV, mvLift_mvDesc_assoc,
    _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenLift_mvOpenDesc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenLift_mvOpenDesc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenLift_mvOpenDesc ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenLift_mvOpenDesc

@[reassoc (attr := simp)]
lemma mvOpenDesc_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    mvOpenDesc R X U V (n + 1) ≫ mvOpenδ R hU hV hUV n = 0 := by
  rw [← _root_.CategoryTheory.cancel_epi (biprodHIso R X U V (n + 1)).hom, ← Category.assoc,
    biprodHIso_hom_mvOpenDesc R X U V hU hV hUV, Category.assoc, supIso_hom_mvOpenδ,
    mvDesc_mvδ_assoc, _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenDesc_mvOpenδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenDesc_mvOpenδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenDesc_mvOpenδ ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenDesc_mvOpenδ

theorem mayerVietoris_exact₁ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenδ R hU hV hUV n) (mvOpenLift R X U V n)
      (mvOpenδ_mvOpenLift R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₁' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (supIso R hU hV hUV (n + 1)) (infIso R X U V n)
    (biprodHIso R X U V n) (supIso_hom_mvOpenδ R hU hV hUV n) (infIso_hom_mvOpenLift R X U V n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₁ ``Submission.DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₁

theorem mayerVietoris_exact₂ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenLift R X U V n) (mvOpenDesc R X U V n)
      (mvOpenLift_mvOpenDesc R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₂' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (infIso R X U V n) (biprodHIso R X U V n) (supIso R hU hV hUV n)
    (infIso_hom_mvOpenLift R X U V n) (biprodHIso_hom_mvOpenDesc R X U V hU hV hUV n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₂ ``Submission.DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₂

theorem mayerVietoris_exact₃ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (n : ℕ) :
    (ShortComplex.mk (mvOpenDesc R X U V (n + 1)) (mvOpenδ R hU hV hUV n)
      (mvOpenDesc_mvOpenδ R hU hV hUV n)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (mv_exact₃' (singSub X U) (singSub X V) R n)
  exact ShortComplex.isoMk (biprodHIso R X U V (n + 1)) (supIso R hU hV hUV (n + 1))
    (infIso R X U V n) (biprodHIso_hom_mvOpenDesc R X U V hU hV hUV (n + 1))
    (supIso_hom_mvOpenδ R hU hV hUV n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₃ ``Submission.DifferentialGeometry.Topology.SingularPair.mayerVietoris_exact₃

lemma mvOpenDesc_eq_zero_of_isZero (n : ℕ) (hU' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) n))
    (hV' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) n)) : mvOpenDesc R X U V n = 0 :=
  IsZero.eq_zero_of_src ((_root_.CategoryTheory.Limits.biprod_isZero_iff _ _).2 ⟨hU', hV'⟩) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenDesc_eq_zero_of_isZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenDesc_eq_zero_of_isZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenDesc_eq_zero_of_isZero ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenDesc_eq_zero_of_isZero

lemma mvOpenLift_eq_zero_of_isZero (n : ℕ) (hU' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) n))
    (hV' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) n)) : mvOpenLift R X U V n = 0 :=
  IsZero.eq_zero_of_tgt ((_root_.CategoryTheory.Limits.biprod_isZero_iff _ _).2 ⟨hU', hV'⟩) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenLift_eq_zero_of_isZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenLift_eq_zero_of_isZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenLift_eq_zero_of_isZero ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenLift_eq_zero_of_isZero

theorem mono_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) (n + 1))) :
    Mono (mvOpenδ R hU hV hUV n) :=
  (mayerVietoris_exact₃ R hU hV hUV n).mono_g (mvOpenDesc_eq_zero_of_isZero R (n + 1) hU' hV')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mono_mvOpenδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mono_mvOpenδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mono_mvOpenδ ``Submission.DifferentialGeometry.Topology.SingularPair.mono_mvOpenδ

theorem epi_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) n)) (hV' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) n)) :
    Epi (mvOpenδ R hU hV hUV n) :=
  (mayerVietoris_exact₁ R hU hV hUV n).epi_f (mvOpenLift_eq_zero_of_isZero R n hU' hV')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.epi_mvOpenδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.epi_mvOpenδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.epi_mvOpenδ ``Submission.DifferentialGeometry.Topology.SingularPair.epi_mvOpenδ

def mvOpenδIsKernel (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) (n + 1))) :
    IsLimit (KernelFork.ofι (mvOpenδ R hU hV hUV n) (mvOpenδ_mvOpenLift R hU hV hUV n)) :=
  haveI := mono_mvOpenδ R hU hV hUV n hU' hV'
  (mayerVietoris_exact₁ R hU hV hUV n).fIsKernel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδIsKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδIsKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδIsKernel ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδIsKernel

theorem isIso_mvOpenδ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) (n + 1)))
    (hU₀ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) n)) (hV₀ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) n)) :
    IsIso (mvOpenδ R hU hV hUV n) :=
  haveI := mono_mvOpenδ R hU hV hUV n hU₁ hV₁
  haveI := epi_mvOpenδ R hU hV hUV n hU₀ hV₀
  _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδ ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδ

def mvOpenδIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (hU₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) (n + 1))) (hV₁ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) (n + 1)))
    (hU₀ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) n)) (hV₀ : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) n)) :
    singularHomology R X (n + 1) ≅ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  @_root_.CategoryTheory.asIso _ _ _ _ _ (isIso_mvOpenδ R hU hV hUV n hU₁ hV₁ hU₀ hV₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδIso ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδIso

def mayerVietorisIsoOfIsZero (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ)
    (h : ∀ k, k = n ∨ k = n + 1 →
      _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) k) ∧ _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) k)) :
    singularHomology R X (n + 1) ≅ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  mvOpenδIso R hU hV hUV n (h (n + 1) (Or.inr rfl)).1 (h (n + 1) (Or.inr rfl)).2
    (h n (Or.inl rfl)).1 (h n (Or.inl rfl)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mayerVietorisIsoOfIsZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mayerVietorisIsoOfIsZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mayerVietorisIsoOfIsZero ``Submission.DifferentialGeometry.Topology.SingularPair.mayerVietorisIsoOfIsZero

def mvOpenBoundaryIsoOfContractible (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) (hn : n ≠ 0) :
    singularHomology R X (n + 1) ≅ singularHomology R (TopCat.of (U ∩ V : Set X)) n :=
  mvOpenδIso R hU hV hUV n (isZero_of_contractible R U (n + 1) n.succ_ne_zero)
    (isZero_of_contractible R V (n + 1) n.succ_ne_zero)
    (isZero_of_contractible R U n hn) (isZero_of_contractible R V n hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenBoundaryIsoOfContractible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenBoundaryIsoOfContractible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenBoundaryIsoOfContractible ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenBoundaryIsoOfContractible

end DifferentialGeometry.Topology.SingularPair
