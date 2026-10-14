import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Normalize

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.ContinuousLinearMap
open scoped _root_.RealInnerProductSpace

namespace DifferentialGeometry.Topology.SphereSeparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def unitSphereTangentProjection (x : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (innerSL ℝ x).smulRight x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection ``Submission.DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection

theorem hasFDerivAt_norm_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    HasFDerivAt (fun y : E => ‖y‖) (innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt
    (by simp [hx])
  convert h using 1
  · funext y
    simp
  · simp only [norm_nonneg, Real.sqrt_sq, one_div, mul_inv_rev]
    rw [hx]
    ext y
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_norm_of_norm_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_norm_of_norm_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_norm_of_norm_eq_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_norm_of_norm_eq_one

theorem hasFDerivAt_normalize_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    HasFDerivAt (fun y : E => ‖y‖⁻¹ • y)
      (unitSphereTangentProjection x) x := by
  have hnorm := hasFDerivAt_norm_of_norm_eq_one hx
  have hinv := (hasFDerivAt_inv' (by simp [hx])).comp x hnorm
  have h := hinv.smul (hasFDerivAt_id x)
  have hderiv :
      (Inv.inv ∘ fun y : E => ‖y‖) x • ContinuousLinearMap.id ℝ E +
          ((-((ContinuousLinearMap.mulLeftRight ℝ ℝ) ‖x‖⁻¹) ‖x‖⁻¹) ∘L
            innerSL ℝ x).smulRight x =
        unitSphereTangentProjection x := by
    ext y
    simp only [unitSphereTangentProjection, Function.comp_apply,
      ContinuousLinearMap.neg_comp, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      neg_apply, sub_apply, ContinuousLinearMap.comp_apply,
      coe_innerSL_apply, ContinuousLinearMap.mulLeftRight_apply, neg_smul]
    rw [hx]
    simp only [inv_one, one_smul, one_mul, mul_one]
    change y + -(_root_.Inner.inner ℝ x y • x) = y - _root_.Inner.inner ℝ x y • x
    rw [sub_eq_add_neg]
  convert h using 1
  · funext y
    rfl
  · exact hderiv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_normalize_of_norm_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_normalize_of_norm_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_normalize_of_norm_eq_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.hasFDerivAt_normalize_of_norm_eq_one

theorem fderiv_normalize_of_norm_eq_one {x : E} (hx : ‖x‖ = 1) :
    fderiv ℝ NormedSpace.normalize x = unitSphereTangentProjection x := by
  rw [show NormedSpace.normalize = (fun y : E => ‖y‖⁻¹ • y) by rfl]
  exact (hasFDerivAt_normalize_of_norm_eq_one hx).fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.fderiv_normalize_of_norm_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.fderiv_normalize_of_norm_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.fderiv_normalize_of_norm_eq_one ``Submission.DifferentialGeometry.Topology.SphereSeparation.fderiv_normalize_of_norm_eq_one


theorem unitSphereTangentProjection_apply_self
    {x : E} (hx : ‖x‖ = 1) :
    unitSphereTangentProjection x x = 0 := by
  simp [unitSphereTangentProjection, hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection_apply_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection_apply_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection_apply_self ``Submission.DifferentialGeometry.Topology.SphereSeparation.unitSphereTangentProjection_apply_self

theorem range_unitSphereTangentProjection
    {x : E} (hx : ‖x‖ = 1) :
    LinearMap.range (unitSphereTangentProjection x).toLinearMap =
      (ℝ ∙ x)ᗮ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change _root_.Inner.inner ℝ x (z - (_root_.Inner.inner ℝ x z) • x) = 0
    rw [inner_sub_right, inner_smul_right]
    rw [real_inner_self_eq_norm_sq, hx]
    simp
  · intro hy
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hy
    refine ⟨y, ?_⟩
    simp [unitSphereTangentProjection, hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_unitSphereTangentProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_unitSphereTangentProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_unitSphereTangentProjection ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_unitSphereTangentProjection

end DifferentialGeometry.Topology.SphereSeparation
