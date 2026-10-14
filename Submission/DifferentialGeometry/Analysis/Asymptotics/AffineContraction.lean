import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

namespace DifferentialGeometry.Analysis

theorem le_pow_mul_add_defect_of_affine_contraction
    {e : ℕ → ℝ} {θ δ : ℝ} (hθ : 0 ≤ θ)
    (hstep : ∀ j, e (j + 1) ≤ θ * e j + (1 - θ) * δ) (k : ℕ) :
    e k ≤ θ ^ k * e 0 + (1 - θ ^ k) * δ := by
  have h := le_geom (u := fun j => e j - δ) hθ k (fun j _ => by
    nlinarith [hstep j])
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.le_pow_mul_add_defect_of_affine_contraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.le_pow_mul_add_defect_of_affine_contraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.le_pow_mul_add_defect_of_affine_contraction ``Submission.DifferentialGeometry.Analysis.le_pow_mul_add_defect_of_affine_contraction

end DifferentialGeometry.Analysis

end
