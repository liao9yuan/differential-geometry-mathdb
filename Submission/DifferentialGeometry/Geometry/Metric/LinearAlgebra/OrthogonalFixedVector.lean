import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma det_adjoint (f : E →ₗ[ℝ] E) : f.adjoint.det = f.det := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis f,
    LinearMap.toMatrix_adjoint]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.det_adjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.det_adjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.det_adjoint ``Submission.DifferentialGeometry.Geometry.det_adjoint


theorem det_sub_one_eq_det_mul (A : E ≃ₗᵢ[ℝ] E) :
    (A.toLinearMap - 1).det = A.toLinearMap.det * (1 - A.toLinearMap).det := by
  have hfactor : A.toLinearMap - 1 =
      A.toLinearMap * (1 - A.symm.toLinearMap) := by
    ext x
    simp
  rw [hfactor, map_mul, ← A.adjoint_toLinearMap_eq_symm]
  have hadj : 1 - A.toLinearMap.adjoint = (1 - A.toLinearMap).adjoint := by
    simp
  rw [hadj, det_adjoint]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.det_sub_one_eq_det_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.det_sub_one_eq_det_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.det_sub_one_eq_det_mul ``Submission.DifferentialGeometry.Geometry.det_sub_one_eq_det_mul

theorem exists_unit_fixed_vector_of_det_ne (A : E ≃ₗᵢ[ℝ] E)
    (hdet : A.toLinearMap.det ≠ (-1 : ℝ) ^ Module.finrank ℝ E) :
    ∃ v : E, ‖v‖ = 1 ∧ A v = v := by
  have hneg : A.toLinearMap - 1 = (-1 : ℝ) • (1 - A.toLinearMap) := by
    module
  have heq := det_sub_one_eq_det_mul A
  rw [hneg, LinearMap.det_smul] at heq
  have hzero : (1 - A.toLinearMap).det = 0 := by
    exact (mul_eq_mul_right_iff.mp heq).resolve_left hdet.symm
  obtain ⟨v, hv, hv0⟩ := (LinearMap.ker (1 - A.toLinearMap)).ne_bot_iff.mp
    (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero)
  have hfix : A v = v := by
    change v - A v = 0 at hv
    exact (sub_eq_zero.mp hv).symm
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, norm_ne_zero_iff.mpr hv0]
  · simp [hfix]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_unit_fixed_vector_of_det_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_unit_fixed_vector_of_det_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_unit_fixed_vector_of_det_ne ``Submission.DifferentialGeometry.Geometry.exists_unit_fixed_vector_of_det_ne

end DifferentialGeometry.Geometry
