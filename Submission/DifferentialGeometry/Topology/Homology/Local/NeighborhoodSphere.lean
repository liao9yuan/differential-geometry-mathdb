import Submission.DifferentialGeometry.Topology.Homology.Local.NeighborhoodReduced
import Submission.DifferentialGeometry.Topology.Homology.Local.Euclidean

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric
namespace DifferentialGeometry.Homology
universe u
variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : E)

private def puncturedTranslationHomeomorph : ({x}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set E) :=
  (Homeomorph.subRight x).subtype (fun y => by
    change y ≠ x ↔ y - x ≠ 0
    exact sub_ne_zero.symm)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.puncturedTranslationHomeomorph
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.puncturedTranslationHomeomorph target :: scope.openDecls } }


def puncturedRadialMap : C(({x}ᶜ : Set E), _root_.Metric.sphere (0 : E) 1) :=
  (puncturedSpaceSphereHomotopyEquiv E).toFun.comp (puncturedTranslationHomeomorph E x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedRadialMap ``Submission.DifferentialGeometry.Homology.puncturedRadialMap


@[simp]
theorem puncturedRadialMap_apply (y : ({x}ᶜ : Set E)) :
    (puncturedRadialMap E x y : E) = ‖y.val - x‖⁻¹ • (y.val - x) :=
  puncturedSpaceSphereHomotopyEquiv_apply E _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedRadialMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedRadialMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedRadialMap_apply ``Submission.DifferentialGeometry.Homology.puncturedRadialMap_apply

variable (U : Set E) (hx : x ∈ U) (hU : IsOpen U)
  {k : Type u} [Ring k] (R : ModuleCat.{u} k)


def puncturedNeighborhoodRadialMap :
    C(({(⟨x,hx⟩ : U)}ᶜ : Set U), _root_.Metric.sphere (0 : E) 1) :=
  (puncturedRadialMap E x).comp
    (relativeSubspaceMap (X := TopCat.of U) (Y := TopCat.of E)
      (TopCat.ofHom (⟨Subtype.val,continuous_subtype_val⟩ : C(U,E)))
      (puncturedNeighborhood_mapsTo (TopCat.of E) U x hx)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap


@[simp]
theorem puncturedNeighborhoodRadialMap_apply (y : ({(⟨x,hx⟩ : U)}ᶜ : Set U)) :
    (puncturedNeighborhoodRadialMap E x U hx y : E) =
      ‖y.val.val - x‖⁻¹ • (y.val.val - x) :=
  puncturedRadialMap_apply E x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_apply ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_apply


def puncturedNeighborhoodSphereHomologyIso [ContractibleSpace U] (n : ℕ) :
    reducedSingularHomology R (TopCat.of ({(⟨x,hx⟩ : U)}ᶜ : Set U)) n ≅
      reducedSingularHomology R (TopCat.of (_root_.Metric.sphere (0 : E) 1)) n :=
  reducedPuncturedNeighborhoodHomologyIso (TopCat.of E) U x hx hU R n ≪≫
    reducedSingularHomologyIso R (X := TopCat.of ({x}ᶜ : Set E))
      (Y := TopCat.of ({0}ᶜ : Set E)) (puncturedTranslationHomeomorph E x).toHomotopyEquiv n ≪≫
      reducedSingularHomologyIso R (X := TopCat.of ({0}ᶜ : Set E))
        (Y := TopCat.of (_root_.Metric.sphere (0 : E) 1)) (puncturedSpaceSphereHomotopyEquiv E) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso


@[simp]
theorem puncturedNeighborhoodSphereHomologyIso_hom [ContractibleSpace U] (n : ℕ) :
    (puncturedNeighborhoodSphereHomologyIso E x U hx hU R n).hom =
      reducedSingularHomologyMap R
        (TopCat.ofHom (puncturedNeighborhoodRadialMap E x U hx)) n := by
  simp only [puncturedNeighborhoodSphereHomologyIso, Iso.trans_hom,
    reducedPuncturedNeighborhoodHomologyIso_hom]
  change reducedSingularHomologyMap R _ n ≫
    (reducedSingularHomologyMap R _ n ≫ reducedSingularHomologyMap R _ n) = _
  rw [← reducedSingularHomologyMap_comp, ← reducedSingularHomologyMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_hom ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_hom

variable {r : ℝ} (hr : 0 < r) (hs : sphere x r ⊆ U)


def puncturedNeighborhoodSphereSection :
    C(_root_.Metric.sphere (0 : E) 1, ({(⟨x,hx⟩ : U)}ᶜ : Set U)) := by
  have hnorm (v : _root_.Metric.sphere (0 : E) 1) : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hmem (v : _root_.Metric.sphere (0 : E) 1) : x + r • v.val ∈ U := hs (by
    rw [_root_.Metric.mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, hnorm, mul_one])
  have hne (v : _root_.Metric.sphere (0 : E) 1) : x + r • v.val ≠ x := by
    intro h
    have hz : r • v.val = 0 := add_left_cancel (h.trans (add_zero x).symm)
    have hn := congrArg _root_.Norm.norm hz
    rw [norm_smul, Real.norm_of_nonneg hr.le, hnorm, mul_one, norm_zero] at hn
    exact hr.ne' hn
  exact ⟨fun v => ⟨⟨x + r • v.val, hmem v⟩,
      fun he => hne v (congrArg Subtype.val he)⟩,
    ((continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection


@[simp]
theorem puncturedNeighborhoodSphereSection_apply (v : _root_.Metric.sphere (0 : E) 1) :
    (puncturedNeighborhoodSphereSection E x U hx hr hs v).val.val = x + r • v.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection_apply ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodSphereSection_apply


theorem puncturedNeighborhoodRadialMap_comp_section :
    (puncturedNeighborhoodRadialMap E x U hx).comp
      (puncturedNeighborhoodSphereSection E x U hx hr hs) = ContinuousMap.id _ := by
  ext v
  change ((puncturedNeighborhoodRadialMap E x U hx)
    (puncturedNeighborhoodSphereSection E x U hx hr hs v) : E) = v.val
  rw [puncturedNeighborhoodRadialMap_apply, puncturedNeighborhoodSphereSection_apply,
    add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le,
    (show ‖v.val‖ = 1 from mem_sphere_zero_iff_norm.mp v.property), mul_one, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_comp_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_comp_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_comp_section ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodRadialMap_comp_section


theorem puncturedNeighborhoodSphereHomologyIso_inv [ContractibleSpace U] (n : ℕ) :
    (puncturedNeighborhoodSphereHomologyIso E x U hx hU R n).inv =
      reducedSingularHomologyMap R
        (TopCat.ofHom (puncturedNeighborhoodSphereSection E x U hx hr hs)) n := by
  apply (_root_.CategoryTheory.cancel_mono (puncturedNeighborhoodSphereHomologyIso E x U hx hU R n).hom).mp
  rw [Iso.inv_hom_id, puncturedNeighborhoodSphereHomologyIso_hom,
    ← reducedSingularHomologyMap_comp]
  have he : (TopCat.ofHom (puncturedNeighborhoodSphereSection E x U hx hr hs)) ≫
      (TopCat.ofHom (puncturedNeighborhoodRadialMap E x U hx)) = 𝟙 (TopCat.of (_root_.Metric.sphere (0 : E) 1)) :=
    congrArg TopCat.ofHom (puncturedNeighborhoodRadialMap_comp_section E x U hx hr hs)
  rw [he, reducedSingularHomologyMap_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_inv ``Submission.DifferentialGeometry.Homology.puncturedNeighborhoodSphereHomologyIso_inv
end DifferentialGeometry.Homology
