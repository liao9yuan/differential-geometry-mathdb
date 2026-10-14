import Submission.DifferentialGeometry.Topology.Homology.SingularPair
import Submission.DifferentialGeometry.Topology.Homology.Naturality
import Submission.DifferentialGeometry.Topology.Homology.MayerVietoris.MayerVietoris
import Submission.DifferentialGeometry.Topology.Homology.Spheres.SphereTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.HomologicalComplex _root_.Submission.HomologicalComplex _root_.AlgebraicTopology
open scoped _root_.ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

section MVone

variable {X : TopCat.{u}} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

abbrev antiDiag : R ⟶ R ⊞ R := biprod.lift (𝟙 R) (-𝟙 R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.antiDiag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.antiDiag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.antiDiag ``Submission.DifferentialGeometry.Topology.SingularPair.antiDiag

instance mono_antiDiag : _root_.CategoryTheory.Mono (antiDiag R) :=
  _root_.CategoryTheory.mono_of_mono_fac (biprod.lift_fst (𝟙 R) (-𝟙 R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mono_antiDiag then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mono_antiDiag"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mono_antiDiag ``Submission.DifferentialGeometry.Topology.SingularPair.mono_antiDiag

lemma mvOpenLift_comp_biprodMap_ε :
    mvOpenLift R X U V 0 ≫ biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)) =
      ε R (TopCat.of (U ∩ V : Set X)) ≫ antiDiag R := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc, mvOpenLift_fst, Category.assoc,
      biprod.lift_fst, Category.comp_id]
    exact ε_natural' R _
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc, mvOpenLift_snd, Category.assoc,
      biprod.lift_snd, Preadditive.comp_neg, Category.comp_id]
    exact (Preadditive.neg_comp _ _).trans (congrArg Neg.neg (ε_natural' R _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenLift_comp_biprodMap_ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenLift_comp_biprodMap_ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenLift_comp_biprodMap_ε ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenLift_comp_biprodMap_ε

@[reassoc (attr := simp)]
lemma mvOpenδ_comp_ε :
    mvOpenδ R hU hV hUV 0 ≫ ε R (TopCat.of (U ∩ V : Set X)) = 0 := by
  have h1 : ε R (TopCat.of (U ∩ V : Set X)) =
      (ε R (TopCat.of (U ∩ V : Set X)) ≫ antiDiag R) ≫ biprod.fst := by
    rw [Category.assoc, biprod.lift_fst, Category.comp_id]
  rw [h1, ← mvOpenLift_comp_biprodMap_ε, ← Category.assoc, ← Category.assoc,
    mvOpenδ_mvOpenLift, _root_.CategoryTheory.Limits.zero_comp, _root_.CategoryTheory.Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδ_comp_ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδ_comp_ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδ_comp_ε ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδ_comp_ε

def mvOpenδred : singularHomology R X 1 ⟶ reducedHomologyZero R (TopCat.of (U ∩ V : Set X)) :=
  kernel.lift _ (mvOpenδ R hU hV hUV 0) (mvOpenδ_comp_ε R hU hV hUV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδred ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδred

@[reassoc (attr := simp)]
lemma mvOpenδred_ι :
    mvOpenδred R hU hV hUV ≫ reducedHomologyZeroInclusion R (TopCat.of (U ∩ V : Set X)) = mvOpenδ R hU hV hUV 0 :=
  kernel.lift_ι _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδred_ι then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδred_ι"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδred_ι ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδred_ι

theorem mono_mvOpenδred (hU' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of U) 1)) (hV' : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of V) 1)) :
    Mono (mvOpenδred R hU hV hUV) :=
  haveI := mono_mvOpenδ R hU hV hUV 0 hU' hV'
  _root_.CategoryTheory.mono_of_mono_fac (mvOpenδred_ι R hU hV hUV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mono_mvOpenδred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mono_mvOpenδred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mono_mvOpenδred ``Submission.DifferentialGeometry.Topology.SingularPair.mono_mvOpenδred

theorem epi_mvOpenδred [_root_.CategoryTheory.IsIso (ε R (TopCat.of U))] [_root_.CategoryTheory.IsIso (ε R (TopCat.of V))] :
    Epi (mvOpenδred R hU hV hUV) := by
  have hex := exact_kernelLift₂₃ (mayerVietoris_exact₁ R hU hV hUV 0)
    (ε R (TopCat.of (U ∩ V : Set X))) (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)))
    (antiDiag R) (mvOpenLift_comp_biprodMap_ε R)
  have hz : _root_.CategoryTheory.Limits.IsZero (_root_.CategoryTheory.Limits.kernel (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V)))) := by
    have : _root_.CategoryTheory.IsIso (biprod.map (ε R (TopCat.of U)) (ε R (TopCat.of V))) :=
      inferInstanceAs
        (_root_.CategoryTheory.IsIso (biprod.mapIso (_root_.CategoryTheory.asIso (ε R (TopCat.of U))) (_root_.CategoryTheory.asIso (ε R (TopCat.of V)))).hom)
    exact (_root_.CategoryTheory.Limits.isZero_zero _).of_iso (kernel.ofMono _)
  exact hex.epi_f (hz.eq_zero_of_tgt _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.epi_mvOpenδred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.epi_mvOpenδred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.epi_mvOpenδred ``Submission.DifferentialGeometry.Topology.SingularPair.epi_mvOpenδred

theorem isIso_mvOpenδred [ContractibleSpace U] [ContractibleSpace V] :
    IsIso (mvOpenδred R hU hV hUV) :=
  haveI := mono_mvOpenδred R hU hV hUV (isZero_of_contractible R U 1 one_ne_zero)
    (isZero_of_contractible R V 1 one_ne_zero)
  haveI := epi_mvOpenδred R hU hV hUV
  _root_.CategoryTheory.isIso_of_mono_of_epi _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδred then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδred"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδred ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_mvOpenδred

def mvOpenδredIso [ContractibleSpace U] [ContractibleSpace V] :
    singularHomology R X 1 ≅ reducedHomologyZero R (TopCat.of (U ∩ V : Set X)) :=
  @_root_.CategoryTheory.asIso _ _ _ _ _ (isIso_mvOpenδred R hU hV hUV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.mvOpenδredIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.mvOpenδredIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.mvOpenδredIso ``Submission.DifferentialGeometry.Topology.SingularPair.mvOpenδredIso

end MVone

section split

variable (X : TopCat.{u})

abbrev εShortComplex : _root_.CategoryTheory.ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk (reducedHomologyZeroInclusion R X) (ε R X) (reducedHomologyZeroInclusion_ε R X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.εShortComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.εShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.εShortComplex ``Submission.DifferentialGeometry.Topology.SingularPair.εShortComplex

lemma εShortComplex_exact : (εShortComplex R X).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (_root_.CategoryTheory.Limits.kernelIsKernel (ε R X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.εShortComplex_exact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.εShortComplex_exact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.εShortComplex_exact ``Submission.DifferentialGeometry.Topology.SingularPair.εShortComplex_exact

variable [Nonempty X]

def ptMap : TopCat.of PUnit.{u + 1} ⟶ X :=
  TopCat.ofHom ⟨fun _ => Classical.arbitrary X, continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.ptMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.ptMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.ptMap ``Submission.DifferentialGeometry.Topology.SingularPair.ptMap

instance isIso_ε_pt : _root_.CategoryTheory.IsIso (ε R (TopCat.of PUnit.{u + 1})) :=
  isIso_ε_of_contractible R PUnit.{u + 1}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.isIso_ε_pt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.isIso_ε_pt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.isIso_ε_pt ``Submission.DifferentialGeometry.Topology.SingularPair.isIso_ε_pt

def εSection : R ⟶ singularHomology R X 0 := _root_.CategoryTheory.inv (ε R (TopCat.of PUnit.{u + 1})) ≫ singularHomologyMap R (ptMap X) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.εSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.εSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.εSection ``Submission.DifferentialGeometry.Topology.SingularPair.εSection

@[reassoc (attr := simp)]
lemma εSection_ε : εSection R X ≫ ε R X = 𝟙 R := by
  rw [εSection, Category.assoc, ε_natural, IsIso.inv_hom_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.εSection_ε then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.εSection_ε"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.εSection_ε ``Submission.DifferentialGeometry.Topology.SingularPair.εSection_ε

def εSplitting : (εShortComplex R X).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _ (εShortComplex_exact R X) (εSection R X)
    (εSection_ε R X) (inferInstance : _root_.CategoryTheory.Mono (reducedHomologyZeroInclusion R X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.εSplitting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.εSplitting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.εSplitting ``Submission.DifferentialGeometry.Topology.SingularPair.εSplitting

def singularHomologyZeroIsoReducedBiprod : singularHomology R X 0 ≅ reducedHomologyZero R X ⊞ R :=
  (εSplitting R X).isoBinaryBiproduct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod

lemma singularHomologyZeroIsoReducedBiprod_hom_snd : (singularHomologyZeroIsoReducedBiprod R X).hom ≫ biprod.snd = ε R X :=
  biprod.lift_snd _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod_hom_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod_hom_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod_hom_snd ``Submission.DifferentialGeometry.Topology.SingularPair.singularHomologyZeroIsoReducedBiprod_hom_snd

lemma inl_singularHomologyZeroIsoReducedBiprod_inv : biprod.inl ≫ (singularHomologyZeroIsoReducedBiprod R X).inv = reducedHomologyZeroInclusion R X :=
  biprod.inl_desc _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.inl_singularHomologyZeroIsoReducedBiprod_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.inl_singularHomologyZeroIsoReducedBiprod_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.inl_singularHomologyZeroIsoReducedBiprod_inv ``Submission.DifferentialGeometry.Topology.SingularPair.inl_singularHomologyZeroIsoReducedBiprod_inv

end split

namespace Sphere

abbrev liftedSphere (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (unitSphere n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.liftedSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.liftedSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.liftedSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.liftedSphere

def uliftSetHomeomorph {Y : Type} [TopologicalSpace Y] (A : Set Y) :
    ↥(ULift.down ⁻¹' A : Set (ULift.{u} Y)) ≃ₜ ↥A :=
  Homeomorph.ulift.sets rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.uliftSetHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.uliftSetHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.uliftSetHomeomorph ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.uliftSetHomeomorph

abbrev liftedNorthPoleComplement (n : ℕ) : Set (ULift.{u} (unitSphere n)) := ULift.down ⁻¹' {northPole n}ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement

abbrev liftedSouthPoleComplement (n : ℕ) : Set (ULift.{u} (unitSphere n)) := ULift.down ⁻¹' {southPole n}ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.liftedSouthPoleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.liftedSouthPoleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.liftedSouthPoleComplement ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.liftedSouthPoleComplement

lemma isOpen_liftedNorthPoleComplement (n : ℕ) : IsOpen (liftedNorthPoleComplement.{u} n) :=
  (isOpen_compl_singleton (northPole n)).preimage continuous_uliftDown

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedNorthPoleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedNorthPoleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedNorthPoleComplement ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedNorthPoleComplement

lemma isOpen_liftedSouthPoleComplement (n : ℕ) : IsOpen (liftedSouthPoleComplement.{u} n) :=
  (isOpen_compl_singleton (southPole n)).preimage continuous_uliftDown

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedSouthPoleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedSouthPoleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedSouthPoleComplement ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isOpen_liftedSouthPoleComplement

lemma liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ (n : ℕ) : liftedNorthPoleComplement.{u} n ∪ liftedSouthPoleComplement.{u} n = Set.univ := by
  rw [← Set.preimage_union, cover, Set.preimage_univ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ

instance contractibleSpace_liftedNorthPoleComplement (n : ℕ) : ContractibleSpace (liftedNorthPoleComplement.{u} n) :=
  (uliftSetHomeomorph _).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedNorthPoleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedNorthPoleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedNorthPoleComplement ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedNorthPoleComplement

instance contractibleSpace_liftedSouthPoleComplement (n : ℕ) : ContractibleSpace (liftedSouthPoleComplement.{u} n) :=
  (uliftSetHomeomorph _).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedSouthPoleComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedSouthPoleComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedSouthPoleComplement ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.contractibleSpace_liftedSouthPoleComplement

def liftedEquatorHomotopyEquiv (n : ℕ) : ↥(liftedNorthPoleComplement.{u} (n + 1) ∩ liftedSouthPoleComplement.{u} (n + 1)) ≃ₕ ULift.{u} (unitSphere n) :=
  (uliftSetHomeomorph (({northPole (n + 1)}ᶜ : Set (unitSphere (n + 1))) ∩ {southPole (n + 1)}ᶜ)).toHomotopyEquiv.trans
    ((equatorHomotopyEquiv n).trans Homeomorph.ulift.symm.toHomotopyEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.liftedEquatorHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.liftedEquatorHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.liftedEquatorHomotopyEquiv ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.liftedEquatorHomotopyEquiv

instance pathConnectedSpace_ulift_succ (n : ℕ) : PathConnectedSpace (ULift.{u} (unitSphere (n + 1))) :=
  Homeomorph.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_ulift_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_ulift_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_ulift_succ ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.pathConnectedSpace_ulift_succ

instance totallyDisconnectedSpace_ulift_zero : TotallyDisconnectedSpace (ULift.{u} (unitSphere 0)) :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.totallyDisconnectedSpace_ulift_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.totallyDisconnectedSpace_ulift_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.totallyDisconnectedSpace_ulift_zero ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.totallyDisconnectedSpace_ulift_zero

theorem isZero_singularHomology_sphere_zero (k : ℕ) (hk : k ≠ 0) : _root_.CategoryTheory.Limits.IsZero (singularHomology R (liftedSphere.{u} 0) k) :=
  _root_.AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ k R (liftedSphere.{u} 0) hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere_zero ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere_zero

def reducedHomologyZeroLiftedZeroSphereIso : reducedHomologyZero R (liftedSphere.{u} 0) ≅ R :=
  reducedHomologyZeroIsoOfTwoPoints R (liftedSphere.{u} 0) ⟨northPole 0⟩ ⟨southPole 0⟩
    (fun h => northPole_ne_southPole 0 (congrArg ULift.down h))
    (fun z => by
      rcases eq_northPole_or_eq_southPole_zero z.down with h | h
      · exact Or.inl (ULift.ext _ _ h)
      · exact Or.inr (ULift.ext _ _ h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroLiftedZeroSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroLiftedZeroSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroLiftedZeroSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroLiftedZeroSphereIso

instance nonempty_ulift_sphere (n : ℕ) : Nonempty (ULift.{u} (unitSphere n)) := ⟨⟨northPole n⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.nonempty_ulift_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.nonempty_ulift_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.nonempty_ulift_sphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.nonempty_ulift_sphere

def singularHomologyZeroLiftedZeroSphereIso : singularHomology R (liftedSphere.{u} 0) 0 ≅ R ⊞ R :=
  singularHomologyZeroIsoReducedBiprod R (liftedSphere.{u} 0) ≪≫ biprod.mapIso (reducedHomologyZeroLiftedZeroSphereIso R) (Iso.refl R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedZeroSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedZeroSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedZeroSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedZeroSphereIso

def singularHomologyLiftedSphereSuccIso (n k : ℕ) : singularHomology R (liftedSphere.{u} (n + 1)) (k + 2) ≅ singularHomology R (liftedSphere.{u} n) (k + 1) :=
  mvOpenBoundaryIsoOfContractible R (isOpen_liftedNorthPoleComplement (n + 1)) (isOpen_liftedSouthPoleComplement (n + 1)) (liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ (n + 1))
    (k + 1) k.succ_ne_zero ≪≫ homologyIso R (liftedEquatorHomotopyEquiv n) (k + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyLiftedSphereSuccIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyLiftedSphereSuccIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyLiftedSphereSuccIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyLiftedSphereSuccIso

def singularHomologyOneLiftedSphereSuccIso (n : ℕ) : singularHomology R (liftedSphere.{u} (n + 1)) 1 ≅ reducedHomologyZero R (liftedSphere.{u} n) :=
  mvOpenδredIso R (isOpen_liftedNorthPoleComplement (n + 1)) (isOpen_liftedSouthPoleComplement (n + 1)) (liftedNorthPoleComplement_union_liftedSouthPoleComplement_eq_univ (n + 1)) ≪≫
    reducedHomologyZeroIso R (liftedEquatorHomotopyEquiv n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyOneLiftedSphereSuccIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyOneLiftedSphereSuccIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyOneLiftedSphereSuccIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyOneLiftedSphereSuccIso

theorem isZero_reducedHomologyZero_sphere_succ (n : ℕ) : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R (liftedSphere.{u} (n + 1))) :=
  isZero_reducedHomologyZero_of_pathConnected R (liftedSphere.{u} (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere_succ ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere_succ

instance isIso_ε_sphere_succ (n : ℕ) : _root_.CategoryTheory.IsIso (ε R (liftedSphere.{u} (n + 1))) :=
  isIso_ε_of_pathConnected R (liftedSphere.{u} (n + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isIso_ε_sphere_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isIso_ε_sphere_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isIso_ε_sphere_succ ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isIso_ε_sphere_succ

def singularHomologyZeroLiftedSphereSuccIso (n : ℕ) : singularHomology R (liftedSphere.{u} (n + 1)) 0 ≅ R :=
  _root_.CategoryTheory.asIso (ε R (liftedSphere.{u} (n + 1)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereSuccIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereSuccIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereSuccIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereSuccIso

theorem homology_sphere_aux (n : ℕ) :
    (∀ k, k ≠ n → k ≠ 0 → _root_.CategoryTheory.Limits.IsZero (singularHomology R (liftedSphere.{u} n) k)) ∧
      (n ≠ 0 → Nonempty (singularHomology R (liftedSphere.{u} n) n ≅ R)) := by
  induction n with
  | zero => exact ⟨fun k _ hk => isZero_singularHomology_sphere_zero R k hk, fun h => absurd rfl h⟩
  | succ n ih =>
    refine ⟨fun k hk hk0 => ?_, fun _ => ?_⟩
    · obtain _ | _ | k := k
      · exact absurd rfl hk0
      · have hn : n ≠ 0 := by omega
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have e := singularHomologyOneLiftedSphereSuccIso R (m + 1)
        exact (isZero_reducedHomologyZero_sphere_succ R m).of_iso e
      · have e := singularHomologyLiftedSphereSuccIso R n k
        exact (ih.1 (k + 1) (by omega) (by omega)).of_iso e
    · obtain _ | n := n
      · exact ⟨singularHomologyOneLiftedSphereSuccIso R 0 ≪≫ reducedHomologyZeroLiftedZeroSphereIso R⟩
      · obtain ⟨e⟩ := ih.2 n.succ_ne_zero
        exact ⟨singularHomologyLiftedSphereSuccIso R (n + 1) n ≪≫ e⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere_aux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere_aux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere_aux ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere_aux

theorem isZero_singularHomology_sphere (n k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) : _root_.CategoryTheory.Limits.IsZero (singularHomology R (liftedSphere.{u} n) k) :=
  (homology_sphere_aux R n).1 k hk hk0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_sphere

def singularHomologyTopLiftedSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R (liftedSphere.{u} n) n ≅ R :=
  Classical.choice ((homology_sphere_aux R n).2 hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopLiftedSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopLiftedSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopLiftedSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopLiftedSphereIso

def singularHomologyZeroLiftedSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R (liftedSphere.{u} n) 0 ≅ R :=
  match n, hn with
  | m + 1, _ => singularHomologyZeroLiftedSphereSuccIso R m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroLiftedSphereIso

theorem isZero_reducedHomologyZero_sphere (n : ℕ) (hn : n ≠ 0) : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R (liftedSphere.{u} n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact isZero_reducedHomologyZero_sphere_succ R m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_sphere

theorem homology_sphere (n k : ℕ) :
    (k = n → n ≠ 0 → Nonempty (singularHomology R (liftedSphere.{u} n) k ≅ R)) ∧
      (k ≠ n → k ≠ 0 → _root_.CategoryTheory.Limits.IsZero (singularHomology R (liftedSphere.{u} n) k)) ∧
      (n ≠ 0 → Nonempty (singularHomology R (liftedSphere.{u} n) 0 ≅ R)) ∧
      (n = 0 → Nonempty (reducedHomologyZero R (liftedSphere.{u} 0) ≅ R)) ∧
      (n = 0 → Nonempty (singularHomology R (liftedSphere.{u} 0) 0 ≅ R ⊞ R)) ∧
      (n ≠ 0 → _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R (liftedSphere.{u} n))) :=
  ⟨fun hk hn => by subst hk; exact ⟨singularHomologyTopLiftedSphereIso R k hn⟩, isZero_singularHomology_sphere R n k,
    fun hn => ⟨singularHomologyZeroLiftedSphereIso R n hn⟩, fun _ => ⟨reducedHomologyZeroLiftedZeroSphereIso R⟩, fun _ => ⟨singularHomologyZeroLiftedZeroSphereIso R⟩,
    isZero_reducedHomologyZero_sphere R n⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.homology_sphere

def homologyIsoSphere {M : Type u} [TopologicalSpace M] {n : ℕ} (e : M ≃ₕ unitSphere n) (k : ℕ) :
    singularHomology R (TopCat.of M) k ≅ singularHomology R (liftedSphere.{u} n) k :=
  homologyIso R (e.trans Homeomorph.ulift.symm.toHomotopyEquiv) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.homologyIsoSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.homologyIsoSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.homologyIsoSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.homologyIsoSphere

def reducedHomologyZeroIsoOfHomotopyEquivSphere {M : Type u} [TopologicalSpace M] {n : ℕ} (e : M ≃ₕ unitSphere n) :
    reducedHomologyZero R (TopCat.of M) ≅ reducedHomologyZero R (liftedSphere.{u} n) :=
  reducedHomologyZeroIso R (e.trans Homeomorph.ulift.symm.toHomotopyEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivSphere

theorem isZero_singularHomology_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) : _root_.CategoryTheory.Limits.IsZero (singularHomology R (TopCat.of M) k) :=
  (isZero_singularHomology_sphere R n k hk hk0).of_iso (homologyIsoSphere R e k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_of_homotopyEquiv_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_of_homotopyEquiv_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_of_homotopyEquiv_sphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_of_homotopyEquiv_sphere

def singularHomologyTopIsoOfHomotopyEquivSphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (hn : n ≠ 0) : singularHomology R (TopCat.of M) n ≅ R :=
  homologyIsoSphere R e n ≪≫ singularHomologyTopLiftedSphereIso R n hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopIsoOfHomotopyEquivSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopIsoOfHomotopyEquivSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopIsoOfHomotopyEquivSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopIsoOfHomotopyEquivSphere

def singularHomologyZeroIsoOfHomotopyEquivSphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (hn : n ≠ 0) : singularHomology R (TopCat.of M) 0 ≅ R :=
  homologyIsoSphere R e 0 ≪≫ singularHomologyZeroLiftedSphereIso R n hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivSphere

theorem isZero_reducedHomologyZero_of_homotopyEquiv_sphere {M : Type u} [TopologicalSpace M] {n : ℕ}
    (e : M ≃ₕ unitSphere n) (hn : n ≠ 0) : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R (TopCat.of M)) :=
  (isZero_reducedHomologyZero_sphere R n hn).of_iso (reducedHomologyZeroIsoOfHomotopyEquivSphere R e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_of_homotopyEquiv_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_of_homotopyEquiv_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_of_homotopyEquiv_sphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_of_homotopyEquiv_sphere

def reducedHomologyZeroIsoOfHomotopyEquivZeroSphere {M : Type u} [TopologicalSpace M]
    (e : M ≃ₕ unitSphere 0) : reducedHomologyZero R (TopCat.of M) ≅ R :=
  reducedHomologyZeroIsoOfHomotopyEquivSphere R e ≪≫ reducedHomologyZeroLiftedZeroSphereIso R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivZeroSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivZeroSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivZeroSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroIsoOfHomotopyEquivZeroSphere

def singularHomologyZeroIsoOfHomotopyEquivZeroSphere {M : Type u} [TopologicalSpace M]
    (e : M ≃ₕ unitSphere 0) : singularHomology R (TopCat.of M) 0 ≅ R ⊞ R :=
  homologyIsoSphere R e 0 ≪≫ singularHomologyZeroLiftedZeroSphereIso R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivZeroSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivZeroSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivZeroSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroIsoOfHomotopyEquivZeroSphere

section univZero

variable (R₀ : ModuleCat.{0} ℤ)

def singularHomologyUliftIso (n k : ℕ) : singularHomology R₀ (TopCat.of (unitSphere n)) k ≅ singularHomology R₀ (liftedSphere.{0} n) k :=
  homologyIsoSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyUliftIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyUliftIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyUliftIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyUliftIso

theorem isZero_singularHomology_unitSphere (n k : ℕ) (hk : k ≠ n) (hk0 : k ≠ 0) :
    IsZero (singularHomology R₀ (TopCat.of (unitSphere n)) k) :=
  isZero_singularHomology_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) k hk hk0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_unitSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_unitSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_unitSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_singularHomology_unitSphere

def singularHomologyTopUnitSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R₀ (TopCat.of (unitSphere n)) n ≅ R₀ :=
  singularHomologyTopIsoOfHomotopyEquivSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopUnitSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopUnitSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopUnitSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyTopUnitSphereIso

def singularHomologyZeroUnitSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology R₀ (TopCat.of (unitSphere n)) 0 ≅ R₀ :=
  singularHomologyZeroIsoOfHomotopyEquivSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitSphereIso

theorem isZero_reducedHomologyZero_unitSphere (n : ℕ) (hn : n ≠ 0) : _root_.CategoryTheory.Limits.IsZero (reducedHomologyZero R₀ (TopCat.of (unitSphere n))) :=
  isZero_reducedHomologyZero_of_homotopyEquiv_sphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere n)) hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_unitSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_unitSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_unitSphere ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.isZero_reducedHomologyZero_unitSphere

def reducedHomologyZeroUnitZeroSphereIso : reducedHomologyZero R₀ (TopCat.of (unitSphere 0)) ≅ R₀ :=
  reducedHomologyZeroIsoOfHomotopyEquivZeroSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroUnitZeroSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroUnitZeroSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroUnitZeroSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.reducedHomologyZeroUnitZeroSphereIso

def singularHomologyZeroUnitZeroSphereIso : singularHomology R₀ (TopCat.of (unitSphere 0)) 0 ≅ R₀ ⊞ R₀ :=
  singularHomologyZeroIsoOfHomotopyEquivZeroSphere R₀ (ContinuousMap.HomotopyEquiv.refl (unitSphere 0))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitZeroSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitZeroSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitZeroSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.singularHomologyZeroUnitZeroSphereIso

def integralHomologyTopUnitSphereIso (n : ℕ) (hn : n ≠ 0) : singularHomology integerCoefficients (TopCat.of (unitSphere n)) n ≅ integerCoefficients :=
  singularHomologyTopUnitSphereIso integerCoefficients n hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SingularPair.Sphere.integralHomologyTopUnitSphereIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SingularPair.Sphere.integralHomologyTopUnitSphereIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SingularPair.Sphere.integralHomologyTopUnitSphereIso ``Submission.DifferentialGeometry.Topology.SingularPair.Sphere.integralHomologyTopUnitSphereIso

end univZero

end Sphere

end DifferentialGeometry.Topology.SingularPair
