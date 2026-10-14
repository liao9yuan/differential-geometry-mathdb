import Submission.DifferentialGeometry.Analysis.ODE.PhaseFlow.Perturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.Set _root_.Topology
open scoped _root_.NNReal _root_.Topology

namespace DifferentialGeometry
namespace PhaseFlow

@[simp] theorem phaseErr_zero : phaseErr 0 = 0 := by
  apply NNReal.eq
  simp [phaseErr]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseErr_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseErr_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseErr_zero ``Submission.DifferentialGeometry.PhaseFlow.phaseErr_zero

theorem phaseErr_cont : Continuous phaseErr := by
  unfold phaseErr
  apply Continuous.subtype_mk
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseErr_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseErr_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseErr_cont ``Submission.DifferentialGeometry.PhaseFlow.phaseErr_cont

theorem phaseErr_tendsto : _root_.Filter.Tendsto phaseErr (nhds 0) (nhds 0) := by
  have h : _root_.Filter.Tendsto phaseErr (nhds (0 : NNReal)) (nhds (phaseErr 0)) :=
    phaseErr_cont.continuousAt
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseErr_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseErr_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseErr_tendsto ``Submission.DifferentialGeometry.PhaseFlow.phaseErr_tendsto

theorem phaseErr_lt_ev {eps : NNReal} (heps : 0 < eps) :
    ∀ᶠ k in nhds 0, phaseErr k < eps :=
  phaseErr_tendsto (Iio_mem_nhds heps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PhaseFlow.phaseErr_lt_ev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PhaseFlow.phaseErr_lt_ev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PhaseFlow.phaseErr_lt_ev ``Submission.DifferentialGeometry.PhaseFlow.phaseErr_lt_ev

end PhaseFlow
end DifferentialGeometry
