import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Entropy.W.Functional

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open _root_.MeasureTheory

variable {M : Type*}

def perelmanPotential (n : Nat) (tau : Real) (u : M → Real) : M → Real :=
  fun x => -Real.log (u x / perelmanDensityPrefactor n tau)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.perelmanPotential

theorem prefactor_pos (n : Nat) {tau : Real} (htau : 0 < tau) :
    0 < perelmanDensityPrefactor n tau := by
  unfold perelmanDensityPrefactor
  exact Real.rpow_pos_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) htau) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.prefactor_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.prefactor_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.prefactor_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.prefactor_pos

theorem log_prefactor (n : Nat) {tau : Real} (htau : 0 < tau) :
    Real.log (perelmanDensityPrefactor n tau) =
      (-(n : Real) / 2) * Real.log (4 * Real.pi * tau) := by
  unfold perelmanDensityPrefactor
  change Real.log ((4 * Real.pi * tau) ^ (-(n : Real) / 2)) = _
  rw [Real.log_rpow (mul_pos (mul_pos (by norm_num) Real.pi_pos) htau)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.log_prefactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.log_prefactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.log_prefactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.log_prefactor

theorem density_potential (n : Nat) {tau : Real} (u : M → Real)
    (htau : 0 < tau) (hu : ∀ x, 0 < u x) :
    perelmanDensity n tau (perelmanPotential n tau u) = u := by
  funext x
  have hpref : 0 < perelmanDensityPrefactor n tau := prefactor_pos n htau
  have hratio : 0 < u x / perelmanDensityPrefactor n tau := div_pos (hu x) hpref
  simp only [perelmanDensity, perelmanPotential, neg_neg, Real.exp_log hratio]
  simpa only [mul_div_assoc] using mul_div_cancel_left₀ (u x) hpref.ne'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.density_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.density_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.density_potential ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.density_potential

theorem weighted_potential [MeasurableSpace M] (mu : _root_.MeasureTheory.Measure M) (n : Nat)
    {tau : Real} (u : M → Real) (htau : 0 < tau) (hu : ∀ x, 0 < u x) :
    perelmanWeightedMeasure mu n tau (perelmanPotential n tau u) =
      mu.withDensity (ENNReal.ofReal ∘ u) := by
  unfold perelmanWeightedMeasure
  rw [density_potential n u htau hu]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_potential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_potential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_potential ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.weighted_potential

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
