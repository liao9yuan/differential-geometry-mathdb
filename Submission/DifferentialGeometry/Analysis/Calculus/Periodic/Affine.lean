import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.UniformSpace.HeineCantor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Function _root_.ContinuousMap

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F]



theorem uniformContinuous_of_continuous_unit_periodic {f : ℝ → F}
    (hc : Continuous f) (hp : _root_.Function.Periodic f 1) : UniformContinuous f := by
  let fbar : C(UnitAddCircle, F) := ⟨hp.lift, hc.quotient_liftOn' _⟩
  have hbar := CompactSpace.uniformContinuous_of_continuous fbar.continuous
  have h := hbar.comp (AddSubgroup.zmultiples (1 : ℝ)).normedMk.uniformContinuous
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.uniformContinuous_of_continuous_unit_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.uniformContinuous_of_continuous_unit_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.uniformContinuous_of_continuous_unit_periodic ``Submission.DifferentialGeometry.Analysis.uniformContinuous_of_continuous_unit_periodic


theorem exists_bound_of_continuous_unit_periodic {f : ℝ → F}
    (hc : Continuous f) (hp : _root_.Function.Periodic f 1) : ∃ B : ℝ, 0 < B ∧ ∀ x, ‖f x‖ ≤ B := by
  let fbar : C(UnitAddCircle, F) := ⟨hp.lift, hc.quotient_liftOn' _⟩
  refine ⟨‖fbar‖ + 1, by positivity, fun x => ?_⟩
  exact (fbar.norm_coe_le_norm (x : UnitAddCircle)).trans (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_bound_of_continuous_unit_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_bound_of_continuous_unit_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_bound_of_continuous_unit_periodic ``Submission.DifferentialGeometry.Analysis.exists_bound_of_continuous_unit_periodic


theorem affinePeriodic_sub_id {ψ : ℝ → ℝ} (hψ : ∀ t, ψ (t + 1) = ψ t + 1) :
    Periodic (fun t => ψ t - t) 1 := by
  intro t
  change ψ (t + 1) - (t + 1) = ψ t - t
  rw [hψ]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.affinePeriodic_sub_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.affinePeriodic_sub_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.affinePeriodic_sub_id ``Submission.DifferentialGeometry.Analysis.affinePeriodic_sub_id



theorem uniformContinuous_affinePeriodic {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hψ : ∀ t, ψ (t + 1) = ψ t + 1) : UniformContinuous ψ := by
  have h := (uniformContinuous_of_continuous_unit_periodic (hc.sub continuous_id)
    (affinePeriodic_sub_id hψ)).add uniformContinuous_id
  simpa only [Pi.sub_apply, id_eq, sub_add_cancel] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.uniformContinuous_affinePeriodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.uniformContinuous_affinePeriodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.uniformContinuous_affinePeriodic ``Submission.DifferentialGeometry.Analysis.uniformContinuous_affinePeriodic

end DifferentialGeometry.Analysis
