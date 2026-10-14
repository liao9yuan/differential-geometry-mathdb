import Submission.DifferentialGeometry.Topology.LocalDegree.SphereMap
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Metric
noncomputable section
namespace DifferentialGeometry.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def linearSphereMap (A : E ≃L[ℝ] F) : C(_root_.Metric.sphere (0 : E) 1, _root_.Metric.sphere (0 : F) 1) :=
  sphereMap A 0 1 A.continuous.continuousOn
    (fun _ _ hy => mt A.map_eq_zero_iff.mp hy) ⟨1, by norm_num, le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereMap ``Submission.DifferentialGeometry.LocalDegree.linearSphereMap


@[simp]
theorem linearSphereMap_apply (A : E ≃L[ℝ] F) (v : _root_.Metric.sphere (0 : E) 1) :
    (linearSphereMap A v : F) = ‖A v‖⁻¹ • A v := by
  simp only [linearSphereMap, sphereMap_apply, zero_add, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereMap_apply ``Submission.DifferentialGeometry.LocalDegree.linearSphereMap_apply


@[simp]
theorem linearSphereMap_symm_apply (A : E ≃L[ℝ] F) (v : _root_.Metric.sphere (0 : E) 1) :
    linearSphereMap A.symm (linearSphereMap A v) = v := by
  apply Subtype.ext
  have hv : (v : E) ≠ 0 := by
    intro h
    have hn := norm_eq_of_mem_sphere v
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hA : ‖A v‖ ≠ 0 := norm_ne_zero_iff.mpr (mt A.map_eq_zero_iff.mp hv)
  simp only [linearSphereMap_apply, map_smul, ContinuousLinearEquiv.symm_apply_apply,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    norm_eq_of_mem_sphere v, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hA, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereMap_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereMap_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereMap_symm_apply ``Submission.DifferentialGeometry.LocalDegree.linearSphereMap_symm_apply


def linearSphereHomeomorph (A : E ≃L[ℝ] F) : _root_.Metric.sphere (0 : E) 1 ≃ₜ _root_.Metric.sphere (0 : F) 1 where
  toFun := linearSphereMap A
  invFun := linearSphereMap A.symm
  left_inv := linearSphereMap_symm_apply A
  right_inv := linearSphereMap_symm_apply A.symm
  continuous_toFun := (linearSphereMap A).continuous
  continuous_invFun := (linearSphereMap A.symm).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereHomeomorph ``Submission.DifferentialGeometry.LocalDegree.linearSphereHomeomorph


@[simp]
theorem linearSphereHomeomorph_apply (A : E ≃L[ℝ] F) (v : _root_.Metric.sphere (0 : E) 1) :
    linearSphereHomeomorph A v = linearSphereMap A v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.linearSphereHomeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.linearSphereHomeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.linearSphereHomeomorph_apply ``Submission.DifferentialGeometry.LocalDegree.linearSphereHomeomorph_apply


theorem sphereMap_linear_eq (A : E ≃L[ℝ] F) (R : ℝ) (r : Set.Ioc (0 : ℝ) R) :
    sphereMap A 0 R A.continuous.continuousOn
      (fun _ _ hy => mt A.map_eq_zero_iff.mp hy) r = linearSphereMap A := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply, zero_add, map_smul, norm_smul,
    Real.norm_of_nonneg r.property.1.le, mul_inv_rev, smul_smul, linearSphereMap_apply]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ r.property.1.ne', mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.sphereMap_linear_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.sphereMap_linear_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.sphereMap_linear_eq ``Submission.DifferentialGeometry.LocalDegree.sphereMap_linear_eq

end DifferentialGeometry.LocalDegree
