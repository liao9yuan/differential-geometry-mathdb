import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace Matrix
open _root_.Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜]

open _root_.Matrix in
theorem inv_smul_field (G : Matrix ι ι 𝕜) (c : 𝕜) :
    (c • G)⁻¹ = c⁻¹ • G⁻¹ := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  by_cases hG : IsUnit G.det
  · let : Invertible c := invertibleOfNonzero hc
    simpa only [invOf_eq_inv] using Matrix.inv_smul G c hG
  · have hscaled : ¬IsUnit (c • G).det := by
      intro hs
      apply hG
      rw [Matrix.det_smul] at hs
      exact isUnit_of_mul_isUnit_right hs
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hscaled,
      Matrix.nonsing_inv_apply_not_isUnit _ hG, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.inv_smul_field then
    throwError "Refusing to shadow existing declaration Matrix.inv_smul_field"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.inv_smul_field ``Submission.Matrix.inv_smul_field

end Matrix
