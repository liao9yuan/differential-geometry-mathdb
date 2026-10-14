import Submission.DifferentialGeometry.Topology.Homology.SingularSubcomplex
import Submission.DifferentialGeometry.Topology.Homology.MayerVietoris.ShortExact
import Submission.DifferentialGeometry.Topology.Homology.Subdivision.SmallSimplices
import Submission.DifferentialGeometry.Topology.Homology.MayerVietoris.MayerVietoris
import Mathlib.Algebra.Homology.HomologySequenceLemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.HomologicalComplex _root_.Submission.HomologicalComplex

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section PairQuasiIso

variable {P P' : SSetPair.{u}} (φ : P ⟶ P')

def pairShortComplexMap : P.chainComplexShortComplex R ⟶ P'.chainComplexShortComplex R :=
  ShortComplex.homMk (SSet.chainComplexMap φ.left R) (SSet.chainComplexMap φ.right R)
    (SSetPair.chainComplexMap φ R)
    (by
      dsimp only [SSetPair.chainComplexShortComplex]
      rw [← Functor.map_comp, ← Functor.map_comp, MorphismProperty.Arrow.w])
    (chainComplexMap_right_chainComplexπ R φ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairShortComplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap ``Submission.DifferentialGeometry.Topology.SingularPair.pairShortComplexMap

@[simp] lemma pairShortComplexMap_τ₁ :
    (pairShortComplexMap R φ).τ₁ = SSet.chainComplexMap φ.left R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₁ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₁"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₁ ``Submission.DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₁

@[simp] lemma pairShortComplexMap_τ₂ :
    (pairShortComplexMap R φ).τ₂ = SSet.chainComplexMap φ.right R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₂ ``Submission.DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₂

@[simp] lemma pairShortComplexMap_τ₃ :
    (pairShortComplexMap R φ).τ₃ = SSetPair.chainComplexMap φ R := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₃ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₃"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₃ ``Submission.DifferentialGeometry.Topology.SingularPair.pairShortComplexMap_τ₃

theorem quasiIso_chainComplexMap_of_quasiIso
    (h₁ : QuasiIso (SSet.chainComplexMap φ.left R))
    (h₂ : QuasiIso (SSet.chainComplexMap φ.right R)) :
    QuasiIso (SSetPair.chainComplexMap φ R) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (pairShortComplexMap R φ)
    (P.shortExact_chainComplexShortComplex R) (P'.shortExact_chainComplexShortComplex R) h₁ h₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIso_chainComplexMap_of_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIso_chainComplexMap_of_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIso_chainComplexMap_of_quasiIso ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIso_chainComplexMap_of_quasiIso

theorem isIso_homologyMap_of_quasiIso
    (h₁ : QuasiIso (SSet.chainComplexMap φ.left R))
    (h₂ : QuasiIso (SSet.chainComplexMap φ.right R)) (n : ℕ) :
    IsIso (SSetPair.homologyMap φ R n) :=
  haveI := quasiIso_chainComplexMap_of_quasiIso R φ h₁ h₂
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_quasiIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_quasiIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_quasiIso ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_quasiIso

instance isIso_homologyMap_of_isIso [_root_.CategoryTheory.IsIso φ] (n : ℕ) : _root_.CategoryTheory.IsIso (SSetPair.homologyMap φ R n) :=
  inferInstanceAs (_root_.CategoryTheory.IsIso ((SSetPair.homologyFunctor.{u} R n).map φ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_isIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_isIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_isIso ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_of_isIso

end PairQuasiIso

variable {X : TopCat.{u}} (U V : Set X)

lemma mapsTo_incl : Set.MapsTo (incl X U) (Subtype.val ⁻¹' V) V := fun _ hx ↦ hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mapsTo_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mapsTo_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mapsTo_incl ``Submission.DifferentialGeometry.Topology.SingularPair.mapsTo_incl

lemma singSub_inter_eq_inf_swap : singSub X (U ∩ V) = singSub X V ⊓ singSub X U := by
  rw [singSub_inf, inf_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singSub_inter_eq_inf_swap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singSub_inter_eq_inf_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singSub_inter_eq_inf_swap ``Submission.DifferentialGeometry.Topology.SingularPair.singSub_inter_eq_inf_swap

def infPairIso :
    SSetPair.of (SSet.Subcomplex.homOfLE (singSub_inter_le_left U V)) ≅
      pairInf (singSub X V) (singSub X U) :=
  MorphismProperty.Arrow.isoMk (SSet.Subcomplex.eqToIso (singSub_inter_eq_inf_swap U V))
    (Iso.refl _) (by
      rw [Iso.refl_hom]
      rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.infPairIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.infPairIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.infPairIso ``Submission.DifferentialGeometry.Topology.SingularPair.infPairIso

@[simp] lemma infPairIso_hom_left :
    (infPairIso U V).hom.left =
      SSet.Subcomplex.homOfLE (singSub_inter_eq_inf_swap U V).le := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.infPairIso_hom_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.infPairIso_hom_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.infPairIso_hom_left ``Submission.DifferentialGeometry.Topology.SingularPair.infPairIso_hom_left

@[simp] lemma infPairIso_hom_right : (infPairIso U V).hom.right = 𝟙 _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.infPairIso_hom_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.infPairIso_hom_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.infPairIso_hom_right ``Submission.DifferentialGeometry.Topology.SingularPair.infPairIso_hom_right

def supPairMap : pairSup (singSub X V) (singSub X U) ⟶ pair X V :=
  SSetPair.homMk (singSubIso X V).hom (singSub X V ⊔ singSub X U).ι (by
    change (singSubIso X V).hom ≫ TopCat.toSSet.map (incl X V) =
      SSet.Subcomplex.homOfLE (le_sup_left : singSub X V ≤ singSub X V ⊔ singSub X U) ≫
        (singSub X V ⊔ singSub X U).ι
    rw [singSubIso_hom_map_incl, SSet.Subcomplex.homOfLE_ι])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.supPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.supPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.supPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.supPairMap

@[simp] lemma supPairMap_left : (supPairMap U V).left = (singSubIso X V).hom := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.supPairMap_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.supPairMap_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.supPairMap_left ``Submission.DifferentialGeometry.Topology.SingularPair.supPairMap_left

@[simp] lemma supPairMap_right : (supPairMap U V).right = (singSub X V ⊔ singSub X U).ι := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.supPairMap_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.supPairMap_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.supPairMap_right ``Submission.DifferentialGeometry.Topology.SingularPair.supPairMap_right

abbrev inclRestr : TopCat.of (Subtype.val ⁻¹' V : Set (TopCat.of U)) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨(mapsTo_incl U V).restrict, by fun_prop⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclRestr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclRestr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclRestr ``Submission.DifferentialGeometry.Topology.SingularPair.inclRestr

lemma pairMap_incl_left :
    (pairMap (incl X U) (mapsTo_incl U V)).left = TopCat.toSSet.map (inclRestr U V) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_incl_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_incl_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_incl_left ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_incl_left

lemma pairMap_incl_right :
    (pairMap (incl X U) (mapsTo_incl U V)).right = TopCat.toSSet.map (incl X U) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_incl_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_incl_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_incl_right ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_incl_right

lemma restrictPairIso_hom_left :
    (restrictPairIso U V).hom.left = (restrictIso U V).hom := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_left ``Submission.DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_left

lemma restrictPairIso_hom_right :
    (restrictPairIso U V).hom.right = (singSubIso X U).inv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_right ``Submission.DifferentialGeometry.Topology.SingularPair.restrictPairIso_hom_right

lemma inclRestr_incl : inclRestr U V ≫ incl X V = inclRestrict U V := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inclRestr_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inclRestr_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inclRestr_incl ``Submission.DifferentialGeometry.Topology.SingularPair.inclRestr_incl

lemma factorisation_left :
    TopCat.toSSet.map (inclRestr U V) =
      (restrictIso U V).hom ≫
        SSet.Subcomplex.homOfLE (singSub_inter_eq_inf_swap U V).le ≫
        SSet.Subcomplex.homOfLE (inf_le_left : singSub X V ⊓ singSub X U ≤ singSub X V) ≫
        (singSubIso X V).hom := by
  rw [← _root_.CategoryTheory.cancel_mono (TopCat.toSSet.map (incl X V)), ← Functor.map_comp, inclRestr_incl,
    Category.assoc, Category.assoc, Category.assoc, singSubIso_hom_map_incl,
    SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.homOfLE_ι, restrictIso_hom_ι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.factorisation_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.factorisation_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.factorisation_left ``Submission.DifferentialGeometry.Topology.SingularPair.factorisation_left

lemma factorisation_right :
    TopCat.toSSet.map (incl X U) =
      (singSubIso X U).inv ≫ 𝟙 _ ≫
        SSet.Subcomplex.homOfLE (le_sup_right : singSub X U ≤ singSub X V ⊔ singSub X U) ≫
        (singSub X V ⊔ singSub X U).ι := by
  rw [Category.id_comp, SSet.Subcomplex.homOfLE_ι, singSubIso_inv_ι]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.factorisation_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.factorisation_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.factorisation_right ``Submission.DifferentialGeometry.Topology.SingularPair.factorisation_right

theorem pairMap_incl_factorisation :
    pairMap (incl X U) (mapsTo_incl U V) =
      (restrictPairIso U V).hom ≫ (infPairIso U V).hom ≫
        excisionPairMap (singSub X V) (singSub X U) ≫ supPairMap U V := by
  apply MorphismProperty.Arrow.Hom.ext
  · simp only [MorphismProperty.Comma.comp_hom, Comma.comp_left]
    exact factorisation_left U V
  · simp only [MorphismProperty.Comma.comp_hom, Comma.comp_right]
    exact factorisation_right U V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.pairMap_incl_factorisation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.pairMap_incl_factorisation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.pairMap_incl_factorisation ``Submission.DifferentialGeometry.Topology.SingularPair.pairMap_incl_factorisation

section excision

variable {U V}

lemma iUnion_interior_coverFam_of_union (h : interior U ∪ interior V = Set.univ) :
    ⋃ b, interior (coverFam X U V b) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ interior U ∪ interior V := h ▸ Set.mem_univ x
  rw [Set.mem_iUnion]
  rcases hx with hx | hx
  · exact ⟨true, hx⟩
  · exact ⟨false, hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam_of_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam_of_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam_of_union ``Submission.DifferentialGeometry.Topology.SingularPair.iUnion_interior_coverFam_of_union

theorem quasiIso_sup_ι (h : interior U ∪ interior V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (singSub X U ⊔ singSub X V).ι R) := by
  rw [← small_coverFam]
  exact quasiIso_smallChainMap R _ (iUnion_interior_coverFam_of_union h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIso_sup_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIso_sup_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIso_sup_ι ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIso_sup_ι

theorem quasiIso_supPairMap_left :
    QuasiIso (SSet.chainComplexMap (supPairMap U V).left R) :=
  quasiIso_of_isIso
    (((SSet.chainComplexFunctor.{u} (ModuleCat.{u} ℤ)).obj R).map (singSubIso X V).hom)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_left ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_left

theorem quasiIso_supPairMap_right (h : interior U ∪ interior V = Set.univ) :
    QuasiIso (SSet.chainComplexMap (supPairMap U V).right R) := by
  rw [supPairMap_right]
  exact quasiIso_sup_ι R (by rwa [Set.union_comm])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_right ``Submission.DifferentialGeometry.Topology.SingularPair.quasiIso_supPairMap_right

theorem isIso_homologyMap_supPairMap (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    IsIso (SSetPair.homologyMap (supPairMap U V) R n) :=
  isIso_homologyMap_of_quasiIso R _ (quasiIso_supPairMap_left R)
    (quasiIso_supPairMap_right R h) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_supPairMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_supPairMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_supPairMap ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_homologyMap_supPairMap

theorem excision (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    IsIso (relativeHomologyMap R (incl X U) (mapsTo_incl U V) n) := by
  have := isIso_homologyMap_supPairMap R h n
  rw [relativeHomologyMap, pairMap_incl_factorisation, SSetPair.homologyMap_comp,
    SSetPair.homologyMap_comp, SSetPair.homologyMap_comp]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excision ``Submission.DifferentialGeometry.Topology.SingularPair.excision

def excisionIso (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    relativeHomology R (TopCat.of U) (Subtype.val ⁻¹' V) n ≅ relativeHomology R X V n :=
  @_root_.CategoryTheory.asIso _ _ _ _ _ (excision R h n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionIso ``Submission.DifferentialGeometry.Topology.SingularPair.excisionIso

lemma excisionIso_hom (h : interior U ∪ interior V = Set.univ) (n : ℕ) :
    (excisionIso R h n).hom = relativeHomologyMap R (incl X U) (mapsTo_incl U V) n := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionIso_hom ``Submission.DifferentialGeometry.Topology.SingularPair.excisionIso_hom

theorem excision_open (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (relativeHomologyMap R (incl X U) (mapsTo_incl U V) n) :=
  excision R (by rwa [hU.interior_eq, hV.interior_eq]) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excision_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excision_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excision_open ``Submission.DifferentialGeometry.Topology.SingularPair.excision_open

def excisionOpenIso (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    relativeHomology R (TopCat.of U) (Subtype.val ⁻¹' V) n ≅ relativeHomology R X V n :=
  @_root_.CategoryTheory.asIso _ _ _ _ _ (excision_open R hU hV hUV n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionOpenIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionOpenIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionOpenIso ``Submission.DifferentialGeometry.Topology.SingularPair.excisionOpenIso

variable (Z A : Set X)

lemma interior_compl_union_interior_of_closure_subset (hZ : closure Z ⊆ interior A) :
    interior Zᶜ ∪ interior A = Set.univ := by
  rw [interior_compl]
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (hZ hx)
  · exact Or.inl hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.interior_compl_union_interior_of_closure_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.interior_compl_union_interior_of_closure_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.interior_compl_union_interior_of_closure_subset ``Submission.DifferentialGeometry.Topology.SingularPair.interior_compl_union_interior_of_closure_subset

theorem excision_closed (hZ : closure Z ⊆ interior A) (n : ℕ) :
    IsIso (relativeHomologyMap R (incl X Zᶜ) (mapsTo_incl Zᶜ A) n) :=
  excision R (interior_compl_union_interior_of_closure_subset Z A hZ) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excision_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excision_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excision_closed ``Submission.DifferentialGeometry.Topology.SingularPair.excision_closed

def excisionClosedIso (hZ : closure Z ⊆ interior A) (n : ℕ) :
    relativeHomology R (TopCat.of (Zᶜ : Set X)) (Subtype.val ⁻¹' A) n ≅ relativeHomology R X A n :=
  @_root_.CategoryTheory.asIso _ _ _ _ _ (excision_closed R Z A hZ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.excisionClosedIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.excisionClosedIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.excisionClosedIso ``Submission.DifferentialGeometry.Topology.SingularPair.excisionClosedIso

end excision

end DifferentialGeometry.Topology.SingularPair
