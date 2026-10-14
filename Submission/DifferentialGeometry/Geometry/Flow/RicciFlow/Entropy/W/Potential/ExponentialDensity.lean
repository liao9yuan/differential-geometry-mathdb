import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

variable {M : Type*}

theorem perelmanDensity_eq_exp_log (n : ℕ) {t : ℝ} (ht : 0 < t) (f : M → ℝ) :
    perelmanDensity n t f = fun x =>
      Real.exp (-f x - (n : ℝ) / 2 * Real.log t - (n : ℝ) / 2 * Real.log (4 * Real.pi)) := by
  funext x
  change perelmanDensityPrefactor n t * Real.exp (-f x) = _
  rw [← Real.exp_log (prefactor_pos n ht), ← Real.exp_add, log_prefactor n ht,
    Real.log_mul (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht.ne']
  congr 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_eq_exp_log then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_eq_exp_log"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_eq_exp_log ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_eq_exp_log

end DifferentialGeometry.PDE.RicciFlow.Entropy
