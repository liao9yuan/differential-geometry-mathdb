import Submission.DifferentialGeometry.Topology.LocalDegree.SphereAntipodal
import Submission.DifferentialGeometry.Topology.LocalDegree.LinearSphere
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.Metric _root_.Submodule
noncomputable section
universe u
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology

variable {E : Type u} [NormedAddCommGroup E]

section Normed
variable [NormedSpace ℝ E]


theorem linearSphereMap_linearIsometryEquiv_apply (A : E ≃ₗᵢ[ℝ] E)
    (x : _root_.Metric.sphere (0 : E) 1) :
    (linearSphereMap A.toContinuousLinearEquiv x : E) = A x := by
  rw [linearSphereMap_apply]
  change ‖A x‖⁻¹ • A x = A x
  rw [A.norm_map, norm_eq_of_mem_sphere x]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_apply ``Submission.DifferentialGeometry.LocalDegree.linearSphereMap_linearIsometryEquiv_apply

end Normed

variable [InnerProductSpace ℝ E]

def unitSphereReflection (v : E) : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : E) 1) :=
  linearSphereMap ((ℝ ∙ v)ᗮ.reflection.toContinuousLinearEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.unitSphereReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.unitSphereReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.unitSphereReflection ``Submission.DifferentialGeometry.LocalDegree.unitSphereReflection


@[simp]
theorem unitSphereReflection_apply (v : E) (x : _root_.Metric.sphere (0 : E) 1) :
    (unitSphereReflection v x : E) = (ℝ ∙ v)ᗮ.reflection x :=
  linearSphereMap_linearIsometryEquiv_apply _ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.unitSphereReflection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.unitSphereReflection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.unitSphereReflection_apply ``Submission.DifferentialGeometry.LocalDegree.unitSphereReflection_apply


@[simp]
theorem unitSphereReflection_normal (v : _root_.Metric.sphere (0 : E) 1) :
    unitSphereReflection (v : E) v = -v := by
  apply Subtype.ext
  rw [unitSphereReflection_apply]
  exact _root_.Submodule.reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ) (v : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.unitSphereReflection_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.unitSphereReflection_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.unitSphereReflection_normal ``Submission.DifferentialGeometry.LocalDegree.unitSphereReflection_normal


theorem unitSphereReflection_injective (v : E) : Function.Injective (unitSphereReflection v) := by
  intro x y h
  apply Subtype.ext
  apply (ℝ ∙ v)ᗮ.reflection.injective
  simpa only [unitSphereReflection_apply] using congrArg Subtype.val h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.unitSphereReflection_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.unitSphereReflection_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.unitSphereReflection_injective ``Submission.DifferentialGeometry.LocalDegree.unitSphereReflection_injective

private theorem reflection_maps_first (v : _root_.Metric.sphere (0 : E) 1) :
    Set.MapsTo (unitSphereReflection (v : E))
      (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1)) := by
  intro x hx
  change unitSphereReflection (v : E) x ≠ -v
  intro h
  exact hx (unitSphereReflection_injective (v : E) (h.trans (unitSphereReflection_normal v).symm))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reflection_maps_first
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reflection_maps_first target :: scope.openDecls } }

private theorem reflection_maps_second (v : _root_.Metric.sphere (0 : E) 1) :
    Set.MapsTo (unitSphereReflection (v : E))
      (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1)) := by
  intro x hx
  have hv : unitSphereReflection (v : E) (-v) = v := by
    apply Subtype.ext
    rw [unitSphereReflection_apply]
    change (ℝ ∙ (v : E))ᗮ.reflection (-(v : E)) = (v : E)
    rw [map_neg, _root_.Submodule.reflection_orthogonalComplement_singleton_eq_neg (𝕜 := ℝ), neg_neg]
  change unitSphereReflection (v : E) x ≠ v
  intro h
  exact hx (unitSphereReflection_injective (v : E) (h.trans hv.symm))

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reflection_maps_second
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reflection_maps_second target :: scope.openDecls } }


def poleOverlapReflection (v : _root_.Metric.sphere (0 : E) 1) :
    TopCat.of (poleIntersection v) ⟶ TopCat.of (poleIntersection v) :=
  relativeSubspaceMap (TopCat.ofHom (unitSphereReflection (v : E)))
    (fun _ hx => ⟨reflection_maps_second v hx.2, reflection_maps_first v hx.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleOverlapReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleOverlapReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleOverlapReflection ``Submission.DifferentialGeometry.LocalDegree.poleOverlapReflection


theorem poleIntersectionHomotopyEquiv_inv_reflection (v : _root_.Metric.sphere (0 : E) 1) :
    TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun ≫ poleOverlapReflection v =
      TopCat.ofHom (poleIntersectionHomotopyEquiv v).invFun := by
  ext x
  change (unitSphereReflection (v : E) ((poleIntersectionHomotopyEquiv v).symm x).val : E) =
    (((poleIntersectionHomotopyEquiv v).symm x).val : E)
  rw [unitSphereReflection_apply, poleIntersectionHomotopyEquiv_symm_apply]
  exact _root_.Submodule.reflection_mem_subspace_eq_self x.val.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_reflection ``Submission.DifferentialGeometry.LocalDegree.poleIntersectionHomotopyEquiv_inv_reflection

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

theorem poleOverlapReflection_reducedHomologyMap (v : _root_.Metric.sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (poleOverlapReflection v) n = 𝟙 _ := by
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  apply (_root_.CategoryTheory.cancel_epi e.inv).mp
  have h := congrArg (fun f => reducedSingularHomologyMap R f n)
    (poleIntersectionHomotopyEquiv_inv_reflection v)
  simp only [reducedSingularHomologyMap_comp] at h
  exact h.trans (Category.comp_id e.inv).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.poleOverlapReflection_reducedHomologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.poleOverlapReflection_reducedHomologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.poleOverlapReflection_reducedHomologyMap ``Submission.DifferentialGeometry.LocalDegree.poleOverlapReflection_reducedHomologyMap

private theorem reflection_poleCover (v : _root_.Metric.sphere (0 : E) 1) :
    ∀ x : _root_.Metric.sphere (0 : E) 1,
      x ∈ (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1)) ∨
      x ∈ (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1)) := by
  intro x
  have h : x ∈ (poleComplement v ⊔ poleComplement (-v)) := by
    rw [poleComplement_sup]
    trivial
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.reflection_poleCover
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.reflection_poleCover target :: scope.openDecls } }


theorem sphereEquatorReducedHomologyIso_reflection (v : _root_.Metric.sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (unitSphereReflection (v : E))) (n + 1) ≫
        (sphereEquatorReducedHomologyIso R v n).hom =
      -(sphereEquatorReducedHomologyIso R v n).hom := by
  have hs := contractibleSpace_poleComplement v
  have ht := contractibleSpace_poleComplement (-v)
  have h := reducedConnectingMap_of_coverExchange R
    (TopCat.ofHom (unitSphereReflection (v : E)))
    (reflection_maps_first v) (reflection_maps_second v)
    (poleComplement v).isOpen (poleComplement (-v)).isOpen (reflection_poleCover v) n
  rw [reducedMayerVietorisConnectingMap_eq_iso] at h
  change _ ≫ (_ ≫ _) = -(_ ≫ _)
  rw [← Category.assoc, h, Preadditive.neg_comp, Category.assoc]
  let e : reducedSingularHomology R (TopCat.of (poleIntersection v)) n ≅
      reducedSingularHomology R (TopCat.of (EquatorialSphere v)) n :=
    reducedSingularHomologyIso R (poleIntersectionHomotopyEquiv v) n
  have hh := congrArg (fun f =>
    (reducedMayerVietorisConnectingIso R (TopCat.of (_root_.Metric.sphere (0 : E) 1))
      (poleComplement v : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement (-v) : Set (_root_.Metric.sphere (0 : E) 1))
      (poleComplement v).isOpen (poleComplement (-v)).isOpen (reflection_poleCover v) n).hom ≫
      (f ≫ e.hom))
    (poleOverlapReflection_reducedHomologyMap R v n)
  simpa only [Category.id_comp] using! congrArg Neg.neg hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_reflection ``Submission.DifferentialGeometry.LocalDegree.sphereEquatorReducedHomologyIso_reflection

theorem unitSphereReflection_reducedHomologyMap_succ (v : _root_.Metric.sphere (0 : E) 1) (n : ℕ) :
    reducedSingularHomologyMap R (TopCat.ofHom (unitSphereReflection (v : E))) (n + 1) =
      -𝟙 _ := by
  apply (_root_.CategoryTheory.cancel_mono (sphereEquatorReducedHomologyIso R v n).hom).mp
  rw [sphereEquatorReducedHomologyIso_reflection, Preadditive.neg_comp, Category.id_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.unitSphereReflection_reducedHomologyMap_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.unitSphereReflection_reducedHomologyMap_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.unitSphereReflection_reducedHomologyMap_succ ``Submission.DifferentialGeometry.LocalDegree.unitSphereReflection_reducedHomologyMap_succ


theorem euclideanSphereDegree_reflection_unit {d : ℕ} (v : EuclideanSphere d) :
    euclideanSphereDegree (unitSphereReflection (v : EuclideanSpace ℝ (Fin (d + 1)))) = -1 := by
  cases d with
  | zero =>
    have hspan : ℝ ∙ (v : EuclideanSpace ℝ (Fin 1)) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        rw [finrank_span_singleton (ne_zero_of_mem_unit_sphere v)]
        simp)
    have heq : unitSphereReflection (v : EuclideanSpace ℝ (Fin 1)) =
        unitSphereAntipodal (EuclideanSpace ℝ (Fin 1)) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      simp only [unitSphereReflection_apply, hspan, _root_.Submodule.top_orthogonal_eq_bot, _root_.Submodule.reflection_bot]
      rfl
    rw [heq, euclideanSphereDegree_antipodal_zero]
  | succ d =>
    unfold euclideanSphereDegree
    rw [unitSphereReflection_reducedHomologyMap_succ]
    change euclideanSphereTopReducedHomologyEquiv (d + 1)
      (-euclideanSphereTopGenerator (d + 1)) = -1
    rw [map_neg, euclideanSphereTopReducedHomologyEquiv_generator]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_unit ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_unit


theorem euclideanSphereDegree_reflection {d : ℕ}
    (v : EuclideanSpace ℝ (Fin (d + 1))) (hv : v ≠ 0) :
    euclideanSphereDegree (unitSphereReflection v) = -1 := by
  let p : EuclideanSphere d := ⟨‖v‖⁻¹ • v, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hspan : ℝ ∙ (p : EuclideanSpace ℝ (Fin (d + 1))) = ℝ ∙ v :=
    _root_.Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))) v
  have h := euclideanSphereDegree_reflection_unit p
  simpa only [unitSphereReflection, hspan] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection

theorem euclideanSphereDegree_hyperplaneReflection {d : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin (d + 1))))
    (hK : Module.finrank ℝ Kᗮ = 1) :
    euclideanSphereDegree (linearSphereMap K.reflection.toContinuousLinearEquiv) = -1 := by
  let b := Module.finBasisOfFinrankEq ℝ Kᗮ hK
  have hv : ((b 0 : Kᗮ) : EuclideanSpace ℝ (Fin (d + 1))) ≠ 0 := by
    intro hz
    exact b.ne_zero 0 (Subtype.ext hz)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hK (b 0).property hv
  have hplane : K = (ℝ ∙ ((b 0 : Kᗮ) : EuclideanSpace ℝ (Fin (d + 1))))ᗮ := by
    rw [← hspan, K.orthogonal_orthogonal]
  exact (congrArg (fun L : Submodule ℝ (EuclideanSpace ℝ (Fin (d + 1))) =>
    euclideanSphereDegree (linearSphereMap L.reflection.toContinuousLinearEquiv)) hplane).trans
      (euclideanSphereDegree_reflection _ hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_hyperplaneReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_hyperplaneReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_hyperplaneReflection ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_hyperplaneReflection


@[simp]
theorem unitSphereReflection_zero :
    unitSphereReflection (0 : E) = ContinuousMap.id (_root_.Metric.sphere (0 : E) 1) := by
  ext x
  rw [unitSphereReflection_apply]
  apply _root_.Submodule.reflection_mem_subspace_eq_self
  rw [_root_.Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.unitSphereReflection_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.unitSphereReflection_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.unitSphereReflection_zero ``Submission.DifferentialGeometry.LocalDegree.unitSphereReflection_zero


theorem euclideanSphereDegree_reflection_zero (d : ℕ) :
    euclideanSphereDegree (unitSphereReflection (0 : EuclideanSpace ℝ (Fin (d + 1)))) = 1 := by
  rw [unitSphereReflection_zero, euclideanSphereDegree_id]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_zero ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereDegree_reflection_zero

end DifferentialGeometry.LocalDegree
