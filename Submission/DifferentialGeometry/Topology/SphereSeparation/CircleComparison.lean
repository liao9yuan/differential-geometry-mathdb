import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homotopy.Equiv
import Submission.DifferentialGeometry.Topology.SphereSeparation.SphereCellularComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory
open _root_.unitInterval

namespace DifferentialGeometry.Topology.SphereSeparation


abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.EuclideanPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.EuclideanPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.EuclideanPlane ``Submission.DifferentialGeometry.Topology.SphereSeparation.EuclideanPlane


abbrev CircleOne := Metric.sphere (0 : EuclideanPlane) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.CircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.CircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.CircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.CircleOne


abbrev PuncturedPlane := ({0}ᶜ : Set EuclideanPlane)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.PuncturedPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.PuncturedPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.PuncturedPlane ``Submission.DifferentialGeometry.Topology.SphereSeparation.PuncturedPlane


noncomputable def puncturedPlaneRadialProjection : C(PuncturedPlane, CircleOne) where
  toFun x := ⟨NormedSpace.normalize x.1, by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun x ↦ norm_ne_zero_iff.mpr x.2)).smul continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection ``Submission.DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection


def circleOneInclusionPuncturedPlane : C(CircleOne, PuncturedPlane) where
  toFun x := ⟨x.1, by
    intro hx
    have hnorm : ‖(x.1 : EuclideanPlane)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using x.2
    rw [hx, norm_zero] at hnorm
    norm_num at hnorm⟩
  continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.circleOneInclusionPuncturedPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.circleOneInclusionPuncturedPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.circleOneInclusionPuncturedPlane ``Submission.DifferentialGeometry.Topology.SphereSeparation.circleOneInclusionPuncturedPlane

@[simp]
theorem puncturedPlaneRadialProjection_circleOneInclusion (x : CircleOne) :
  puncturedPlaneRadialProjection (circleOneInclusionPuncturedPlane x) = x := by
  apply Subtype.ext
  change NormedSpace.normalize x.1 = x.1
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (by simpa only [mem_sphere_zero_iff_norm] using x.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection_circleOneInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection_circleOneInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection_circleOneInclusion ``Submission.DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialProjection_circleOneInclusion

private theorem radialHomotopyCoefficient_pos
    (t : unitInterval) (x : PuncturedPlane) :
    0 < (1 - (t : ℝ)) * ‖(x.1 : EuclideanPlane)‖⁻¹ + (t : ℝ) := by
  have hnorm : 0 < ‖(x.1 : EuclideanPlane)‖ := norm_pos_iff.mpr x.2
  by_cases ht : (t : ℝ) = 1
  · simp [ht]
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    have hone : 0 < 1 - (t : ℝ) := sub_pos.mpr htlt
    have hinv : 0 < ‖(x.1 : EuclideanPlane)‖⁻¹ := inv_pos.mpr hnorm
    exact add_pos_of_pos_of_nonneg (mul_pos hone hinv) t.2.1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.radialHomotopyCoefficient_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.radialHomotopyCoefficient_pos target :: scope.openDecls } }

noncomputable def puncturedPlaneRadialHomotopy :
    ContinuousMap.Homotopy
      (circleOneInclusionPuncturedPlane.comp puncturedPlaneRadialProjection)
      (ContinuousMap.id PuncturedPlane) where
  toFun tx :=
    ⟨((1 - (tx.1 : ℝ)) * ‖(tx.2.1 : EuclideanPlane)‖⁻¹ + (tx.1 : ℝ)) • tx.2.1,
      by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        apply norm_ne_zero_iff.mp
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (radialHomotopyCoefficient_pos tx.1 tx.2)]
        exact mul_ne_zero (radialHomotopyCoefficient_pos tx.1 tx.2).ne'
          (norm_ne_zero_iff.mpr tx.2.2)⟩
  continuous_toFun := by
    have ht : Continuous (fun tx : unitInterval × PuncturedPlane ↦ (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous
        (fun tx : unitInterval × PuncturedPlane ↦ (tx.2.1 : EuclideanPlane)) :=
      continuous_subtype_val.comp continuous_snd
    have hnorm : Continuous
        (fun tx : unitInterval × PuncturedPlane ↦ ‖(tx.2.1 : EuclideanPlane)‖) :=
      hx.norm
    have hinv : Continuous
        (fun tx : unitInterval × PuncturedPlane ↦ ‖(tx.2.1 : EuclideanPlane)‖⁻¹) :=
      hnorm.inv₀ (fun tx ↦ norm_ne_zero_iff.mpr tx.2.2)
    apply Continuous.subtype_mk
    exact ((continuous_const.sub ht).mul hinv |>.add ht).smul hx
  map_zero_left x := by
    apply Subtype.ext
    dsimp [puncturedPlaneRadialProjection, circleOneInclusionPuncturedPlane,
      NormedSpace.normalize]
    change ((1 - (0 : ℝ)) * ‖(x.1 : EuclideanPlane)‖⁻¹ + 0) • x.1 =
      ‖(x.1 : EuclideanPlane)‖⁻¹ • x.1
    simp
  map_one_left x := by
    apply Subtype.ext
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialHomotopy ``Submission.DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneRadialHomotopy

noncomputable def puncturedPlaneHomotopyEquivCircleOne :
    ContinuousMap.HomotopyEquiv PuncturedPlane CircleOne where
  toFun := puncturedPlaneRadialProjection
  invFun := circleOneInclusionPuncturedPlane
  left_inv := ⟨puncturedPlaneRadialHomotopy⟩
  right_inv := by
    rw [show puncturedPlaneRadialProjection.comp circleOneInclusionPuncturedPlane =
      ContinuousMap.id CircleOne by
        apply ContinuousMap.ext
        intro x
        exact puncturedPlaneRadialProjection_circleOneInclusion x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneHomotopyEquivCircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneHomotopyEquivCircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneHomotopyEquivCircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.puncturedPlaneHomotopyEquivCircleOne

noncomputable def singularChainsPuncturedPlaneHomotopyEquivCircleOne :
    HomotopyEquiv
      (integerSingularChains (TopCat.of PuncturedPlane))
      (integerSingularChains (TopCat.of CircleOne)) :=
  singularChainHomotopyEquivOfHomotopyEquiv
    puncturedPlaneHomotopyEquivCircleOne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsPuncturedPlaneHomotopyEquivCircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsPuncturedPlaneHomotopyEquivCircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsPuncturedPlaneHomotopyEquivCircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsPuncturedPlaneHomotopyEquivCircleOne

def euclideanPlanePunctureHomeomorphPuncturedPlane (a : EuclideanPlane) :
    ({a}ᶜ : Set EuclideanPlane) ≃ₜ PuncturedPlane :=
  (Homeomorph.subRight a).subtype (by
    intro x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
      Homeomorph.coe_subRight, sub_ne_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomeomorphPuncturedPlane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomeomorphPuncturedPlane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomeomorphPuncturedPlane ``Submission.DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomeomorphPuncturedPlane

noncomputable def euclideanPlanePunctureHomotopyEquivCircleOne
    (a : EuclideanPlane) :
    ContinuousMap.HomotopyEquiv ({a}ᶜ : Set EuclideanPlane) CircleOne :=
  (euclideanPlanePunctureHomeomorphPuncturedPlane a).toHomotopyEquiv.trans
    puncturedPlaneHomotopyEquivCircleOne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomotopyEquivCircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomotopyEquivCircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomotopyEquivCircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.euclideanPlanePunctureHomotopyEquivCircleOne

noncomputable def singularChainsEuclideanPlanePunctureHomotopyEquivCircleOne
    (a : EuclideanPlane) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({a}ᶜ : Set EuclideanPlane)))
      (integerSingularChains (TopCat.of CircleOne)) :=
  singularChainHomotopyEquivOfHomotopyEquiv
    (euclideanPlanePunctureHomotopyEquivCircleOne a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsEuclideanPlanePunctureHomotopyEquivCircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsEuclideanPlanePunctureHomotopyEquivCircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsEuclideanPlanePunctureHomotopyEquivCircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsEuclideanPlanePunctureHomotopyEquivCircleOne

def twoPointComplHomeomorphNestedCompl
    {X : Type} [TopologicalSpace X] (p q : X) (hpq : p ≠ q) :
    ({p, q}ᶜ : Set X) ≃ₜ
      ({(⟨q, hpq.symm⟩ : ({p}ᶜ : Set X))}ᶜ : Set ({p}ᶜ : Set X)) where
  toFun x := ⟨⟨x.1, by
      have hx : x.1 ≠ p ∧ x.1 ≠ q := by
        constructor
        · intro h
          exact x.2 (by simp [h])
        · intro h
          exact x.2 (by simp [h])
      exact hx.1⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff]
        have hx : x.1 ≠ p ∧ x.1 ≠ q := by
          constructor
          · intro h
            exact x.2 (by simp [h])
          · intro h
            exact x.2 (by simp [h])
        exact hx.2⟩
  invFun x := ⟨x.1.1, by
    have hxp : x.1.1 ≠ p := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.1.2
    have hxq : x.1.1 ≠ q := by
      intro hx
      apply x.2
      apply Subtype.ext
      exact hx
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or]
    exact ⟨hxp, hxq⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.twoPointComplHomeomorphNestedCompl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.twoPointComplHomeomorphNestedCompl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.twoPointComplHomeomorphNestedCompl ``Submission.DifferentialGeometry.Topology.SphereSeparation.twoPointComplHomeomorphNestedCompl

noncomputable def sphereTwoTwoPointComplHomotopyEquivCircleOne
    (p q : SphereTwo) (hpq : p ≠ q) :
    ContinuousMap.HomotopyEquiv ({p, q}ᶜ : Set SphereTwo) CircleOne := by
  let qp : ({p}ᶜ : Set SphereTwo) := ⟨q, by simp [hpq.symm]⟩
  let e := sphereTwoPunctureHomeomorph p
  let a : EuclideanPlane := e qp
  let er : ({qp}ᶜ : Set ({p}ᶜ : Set SphereTwo)) ≃ₜ
      ({a}ᶜ : Set EuclideanPlane) :=
    e.subtype (by
      intro x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hx h
        exact hx (e.injective h)
      · intro hx h
        exact hx (congr_arg e h))
  exact ((twoPointComplHomeomorphNestedCompl p q hpq).trans er).toHomotopyEquiv.trans
    (euclideanPlanePunctureHomotopyEquivCircleOne a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sphereTwoTwoPointComplHomotopyEquivCircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sphereTwoTwoPointComplHomotopyEquivCircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sphereTwoTwoPointComplHomotopyEquivCircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.sphereTwoTwoPointComplHomotopyEquivCircleOne

noncomputable def singularChainsSphereTwoTwoPointComplHomotopyEquivCircleOne
    (p q : SphereTwo) (hpq : p ≠ q) :
    HomotopyEquiv
      (integerSingularChains (TopCat.of ({p, q}ᶜ : Set SphereTwo)))
      (integerSingularChains (TopCat.of CircleOne)) :=
  singularChainHomotopyEquivOfHomotopyEquiv
    (sphereTwoTwoPointComplHomotopyEquivCircleOne p q hpq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoTwoPointComplHomotopyEquivCircleOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoTwoPointComplHomotopyEquivCircleOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoTwoPointComplHomotopyEquivCircleOne ``Submission.DifferentialGeometry.Topology.SphereSeparation.singularChainsSphereTwoTwoPointComplHomotopyEquivCircleOne

end DifferentialGeometry.Topology.SphereSeparation
