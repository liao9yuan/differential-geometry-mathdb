import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

theorem hasDerivAt_gaussian_normalization (n : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s : ℝ => Real.exp (-(n / 2) * Real.log s -
        (n / 2) * Real.log (4 * Real.pi)))
      (-(n / (2 * t)) * Real.exp (-(n / 2) * Real.log t -
        (n / 2) * Real.log (4 * Real.pi))) t := by
  have h := (((Real.hasDerivAt_log ht.ne').const_mul (-(n / 2))).sub_const
    ((n / 2) * Real.log (4 * Real.pi))).exp
  apply h.congr_deriv
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.hasDerivAt_gaussian_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.hasDerivAt_gaussian_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.hasDerivAt_gaussian_normalization ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.hasDerivAt_gaussian_normalization

end DifferentialGeometry.Analysis.Parabolic.Euclidean
