import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Potential.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

variable {M : Type*}

theorem potential_density (n : ℕ) {tau : ℝ} (htau : 0 < tau) (f : M → ℝ) :
    perelmanPotential n tau (perelmanDensity n tau f) = f := by
  funext x
  have hpref := (prefactor_pos n htau).ne'
  simp only [perelmanPotential, perelmanDensity]
  rw [mul_div_cancel_left₀ _ hpref, Real.log_exp, neg_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.potential_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.potential_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.potential_density ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.potential_density

theorem perelmanDensity_injective (n : ℕ) {tau : ℝ} (htau : 0 < tau) :
    Function.Injective (perelmanDensity (M := M) n tau) := by
  intro f g h
  have hh := congrArg (perelmanPotential n tau) h
  simpa only [potential_density n htau] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_injective ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanDensity_injective

end DifferentialGeometry.PDE.RicciFlow.Entropy
