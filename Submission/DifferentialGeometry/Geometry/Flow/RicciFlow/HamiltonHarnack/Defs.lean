import Submission.DifferentialGeometry.Tensor.Alternating.Wedge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped _root_.BigOperators

structure HarnackClock where
  origin : Real
  time : Real
  origin_lt_time : origin < time

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock

namespace HarnackClock

def elapsed (clock : HarnackClock) : Real :=
  clock.time - clock.origin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed

theorem elapsed_pos (clock : HarnackClock) : 0 < clock.elapsed := by
  exact sub_pos.mpr clock.origin_lt_time

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_pos

theorem elapsed_ne_zero (clock : HarnackClock) : clock.elapsed ≠ 0 :=
  ne_of_gt clock.elapsed_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_ne_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock.elapsed_ne_zero

theorem origin_ne_time (clock : HarnackClock) : clock.origin ≠ clock.time :=
  ne_of_lt clock.origin_lt_time

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock.origin_ne_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock.origin_ne_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock.origin_ne_time ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock.origin_ne_time

theorem one_div_elapsed_pos (clock : HarnackClock) : 0 < 1 / clock.elapsed := by
  exact one_div_pos.mpr clock.elapsed_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock.one_div_elapsed_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock.one_div_elapsed_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock.one_div_elapsed_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock.one_div_elapsed_pos

theorem not_exists_at_same_time (t : Real) :
    ¬Nonempty {clock : HarnackClock // clock.origin = t ∧ clock.time = t} := by
  intro h
  obtain ⟨clock⟩ := h
  exact clock.1.origin_ne_time (clock.2.1.trans clock.2.2.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HarnackClock.not_exists_at_same_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HarnackClock.not_exists_at_same_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HarnackClock.not_exists_at_same_time ``Submission.DifferentialGeometry.PDE.RicciFlow.HarnackClock.not_exists_at_same_time

end HarnackClock

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]

abbrev HamiltonHarnackTwoForm (V : Type*) [NormedAddCommGroup V]
    [NormedSpace Real V] :=
  V [⋀^Fin 2]→L[Real] Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackTwoForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackTwoForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackTwoForm ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackTwoForm

abbrev HamiltonHarnackCarrier (V : Type*) [NormedAddCommGroup V]
    [NormedSpace Real V] :=
  HamiltonHarnackTwoForm V × StrongDual Real V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackCarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonHarnackCarrier

noncomputable def normalizedWedge (A B : StrongDual Real V) :
    HamiltonHarnackTwoForm V :=
  (2 : Real)⁻¹ •
    ContinuousAlternatingMap.uncurryFin
      (A.smulRight
        (ContinuousAlternatingMap.ofSubsingleton Real V Real (0 : Fin 1) B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.normalizedWedge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.normalizedWedge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.normalizedWedge ``Submission.DifferentialGeometry.PDE.RicciFlow.normalizedWedge

theorem normalizedWedge_apply (A B : StrongDual Real V) (v : Fin 2 -> V) :
    normalizedWedge A B v =
      (1 / 2 : Real) * (A (v 0) * B (v 1) - A (v 1) * B (v 0)) := by
  simp [normalizedWedge, ContinuousAlternatingMap.uncurryFin_apply,
    Fin.sum_univ_two, Fin.removeNth, sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.normalizedWedge_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.normalizedWedge_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.normalizedWedge_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.normalizedWedge_apply

end DifferentialGeometry.PDE.RicciFlow
