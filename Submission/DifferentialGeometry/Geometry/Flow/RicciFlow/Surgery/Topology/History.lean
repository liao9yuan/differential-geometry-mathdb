import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u


structure InitialIdentification (P : OrientedThreeStage.{u}) (g : P.Metric)
    (H : ObservedHistory.{u}) where
  map : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ (H.stage 0).Carrier
  positive : PreservesTangentOrientation P.orientation (H.stage 0).orientation map
  metric_eq : ∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
    (H.initialMetric 0).inner (map x)
        (mfderiv ThreeModel ThreeModel map x v)
        (mfderiv ThreeModel ThreeModel map x w) = g.inner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

namespace ObservedHistory

def atZero (P : OrientedThreeStage.{u}) (g : P.Metric) : ObservedHistory.{u} where
  horizon := 0
  horizon_nonneg := le_rfl
  eventCount := 0
  time := fun _ => 0
  time_strictMono := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega
  time_zero := rfl
  time_le_horizon := le_rfl
  stage := fun _ => P
  initialMetric := fun _ => g
  event i := Fin.elim0 i
  event_initial i := Fin.elim0 i
  event_output i := Fin.elim0 i
  finalSlab h := False.elim ((lt_irrefl (0 : ℝ)) h)
  final_initial h := False.elim ((lt_irrefl (0 : ℝ)) h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.atZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.atZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.atZero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.atZero


theorem incoming_nonempty (H : ObservedHistory.{u}) (i : Fin H.eventCount) :
    Nonempty (H.stage i.castSucc).Carrier :=
  (H.event i).transition.source_nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.incoming_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.incoming_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.incoming_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.incoming_nonempty

theorem empty_stage_is_last (H : ObservedHistory.{u})
    (j : Fin (H.eventCount + 1)) [IsEmpty (H.stage j).Carrier] :
    j = Fin.last H.eventCount := by
  apply Fin.ext
  by_contra hne
  change j.val ≠ H.eventCount at hne
  have hj : j.val < H.eventCount := by
    have hbound := j.isLt
    omega
  let i : Fin H.eventCount := ⟨j.val, hj⟩
  have he : i.castSucc = j := Fin.ext rfl
  have hn : Nonempty (H.stage j).Carrier := he ▸ H.incoming_nonempty i
  exact not_nonempty_iff.mpr inferInstance hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_stage_is_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_stage_is_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_stage_is_last ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_stage_is_last

theorem eventCount_eq_zero_of_horizon_zero (H : ObservedHistory.{u})
    (horizon_zero : H.horizon = 0) : H.eventCount = 0 := by
  by_contra hne
  have hn : 0 < H.eventCount := Nat.pos_of_ne_zero hne
  have htime : H.time 0 < H.time (Fin.last H.eventCount) :=
    H.time_strictMono (by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using hn)
  rw [H.time_zero] at htime
  have hle := H.time_le_horizon
  rw [horizon_zero] at hle
  exact (not_lt_of_ge hle) htime

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_eq_zero_of_horizon_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_eq_zero_of_horizon_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_eq_zero_of_horizon_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_eq_zero_of_horizon_zero

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
