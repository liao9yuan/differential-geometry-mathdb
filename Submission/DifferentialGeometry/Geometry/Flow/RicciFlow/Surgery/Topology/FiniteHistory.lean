import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricEvent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryExtension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Topology (ClosedOrientedManifold FiniteCutCapTrace)
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

structure FiniteSurgeryHistory where
  eventCount : ℕ
  eventCount_pos : 0 < eventCount
  time : Fin (eventCount + 1) → ℝ
  time_strictMono : StrictMono time
  time_zero : time 0 = 0
  stage : Fin (eventCount + 1) → ClosedOrientedManifold.{u} 3
  initialMetric : (i : Fin (eventCount + 1)) → SmoothRiemannianMetric (𝓡 3) (stage i).Carrier
  event : (i : Fin eventCount) →
    MetricCutCapEvent (stage i.castSucc) (stage i.succ) (time i.castSucc) (time i.succ)
  event_initial : ∀ i : Fin eventCount,
    (event i).incoming.flow.base.metric (time i.castSucc) = initialMetric i.castSucc
  event_output : ∀ i : Fin eventCount, (event i).outputMetric = initialMetric i.succ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory

namespace FiniteSurgeryHistory

variable (H : FiniteSurgeryHistory.{u})

def cutCapTrace : FiniteCutCapTrace.{u} where
  eventCount := H.eventCount
  eventCount_pos := H.eventCount_pos
  stage := H.stage
  transition i := (H.event i).transition

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.cutCapTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.cutCapTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.cutCapTrace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.cutCapTrace

def terminalTime : ℝ := H.time (Fin.last H.eventCount)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime

def extinctAt (T : ℝ) : Prop :=
  T = H.terminalTime ∧ IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinctAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinctAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinctAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinctAt

def controlledBy
    (D : (M : ClosedOrientedManifold.{u} 3) → ConnectedComponents M.Carrier → Prop) : Prop :=
  H.cutCapTrace.controlledBy D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.controlledBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.controlledBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.controlledBy ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.controlledBy

structure InitialIdentification (M : ClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) where
  diffeomorph : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (H.stage 0).Carrier
  orientation_preserving : diffeomorph.preservesOrientation M.orientation (H.stage 0).orientation
  metric_eq : ∀ x : M.Carrier, ∀ v w : TangentSpace (𝓡 3) x,
    (H.initialMetric 0).inner (diffeomorph x)
      (mfderiv (𝓡 3) (𝓡 3) diffeomorph x v)
      (mfderiv (𝓡 3) (𝓡 3) diffeomorph x w) = g.inner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification

def InitialIdentification.cutCapIdentification
    {M : ClosedOrientedManifold.{u} 3} {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (f : H.InitialIdentification M g) : H.cutCapTrace.InitialIdentification M :=
  ⟨f.diffeomorph, f.orientation_preserving⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification.cutCapIdentification then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification.cutCapIdentification"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification.cutCapIdentification ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.InitialIdentification.cutCapIdentification

theorem stage_nonempty (i : Fin H.eventCount) : Nonempty (H.stage i.castSucc).Carrier :=
  (H.event i).transition.source_nonempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.stage_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.stage_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.stage_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.stage_nonempty

theorem terminalTime_pos : 0 < H.terminalTime := by
  rw [← H.time_zero]
  apply H.time_strictMono
  exact H.eventCount_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.terminalTime_pos

theorem extinct_trace {T : ℝ} (h : H.extinctAt T) : H.cutCapTrace.extinct := h.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_trace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.extinct_trace

end FiniteSurgeryHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery

noncomputable section
open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u



abbrev FiniteSurgeryHistory :=
  {H : ObservedHistory.{u} // 0 < H.eventCount ∧ H.horizon = H.time (Fin.last H.eventCount)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteSurgeryHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteSurgeryHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteSurgeryHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FiniteSurgeryHistory

namespace ObservedHistory

variable (H : ObservedHistory.{u})


theorem restrict_last_eventCount :
    (H.restrict (H.stageTime (Fin.last H.eventCount))).eventCount = H.eventCount := by
  rw [restrict_eventCount, stageTime, activeStage_at_time]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_last_eventCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_last_eventCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_last_eventCount ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_last_eventCount


theorem eventCount_pos_of_final_empty [Nonempty (H.stage 0).Carrier]
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] : 0 < H.eventCount := by
  apply Nat.pos_of_ne_zero
  intro hn
  have he : Fin.last H.eventCount = (0 : Fin (H.eventCount + 1)) := Fin.ext hn
  have hne : Nonempty (H.stage (Fin.last H.eventCount)).Carrier := he ▸ inferInstance
  exact not_nonempty_iff.mpr inferInstance hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_pos_of_final_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_pos_of_final_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_pos_of_final_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_pos_of_final_empty


theorem last_time_pos (hn : 0 < H.eventCount) : 0 < H.time (Fin.last H.eventCount) := by
  rw [← H.time_zero]
  exact H.time_strictMono (by simpa only [Fin.lt_def, Fin.val_zero, Fin.val_last] using hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.last_time_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.last_time_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.last_time_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.last_time_pos



def toFiniteHistory (hn : 0 < H.eventCount) : FiniteSurgeryHistory.{u} := by
  let F := H.restrict (H.stageTime (Fin.last H.eventCount))
  have hc : F.eventCount = H.eventCount := H.restrict_last_eventCount
  refine ⟨F, hc ▸ hn, ?_⟩
  change H.time (Fin.last H.eventCount) =
    H.time (Fin.castLE _ (Fin.last F.eventCount))
  congr 1
  exact Fin.ext hc.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory


@[simp] theorem toFiniteHistory_eventCount (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.eventCount = H.eventCount := H.restrict_last_eventCount

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_eventCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_eventCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_eventCount ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_eventCount


@[simp] theorem toFiniteHistory_horizon (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.horizon = H.time (Fin.last H.eventCount) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_horizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_horizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_horizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_horizon


theorem toFiniteHistory_finalStage (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.stage (Fin.last (H.toFiniteHistory hn).1.eventCount) =
      H.stage (Fin.last H.eventCount) := by
  change H.stage (Fin.castLE _ (Fin.last (H.toFiniteHistory hn).1.eventCount)) = _
  apply congrArg H.stage
  exact Fin.ext (H.toFiniteHistory_eventCount hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_finalStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_finalStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_finalStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_finalStage


theorem toFiniteHistory_isPrefixOf (hn : 0 < H.eventCount) :
    (H.toFiniteHistory hn).1.IsPrefixOf H := H.restrict_isPrefixOf _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_isPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_isPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_isPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_isPrefixOf




theorem toFiniteHistory_discards
    (hn : 0 < H.eventCount) (D : OrientedThreeStage.{u} → Prop)
    (hD : ∀ i : Fin H.eventCount, D (H.event i).discarded) :
    ∀ i : Fin (H.toFiniteHistory hn).1.eventCount,
      D ((H.toFiniteHistory hn).1.event i).discarded := by
  intro i
  exact hD (Fin.castLE _ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_discards then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_discards"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_discards ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.toFiniteHistory_discards



theorem exists_extinct_finiteHistory [Nonempty (H.stage 0).Carrier]
    [IsEmpty (H.stage (Fin.last H.eventCount)).Carrier] :
    ∃ F : FiniteSurgeryHistory.{u},
      F.1 = H.restrict (H.stageTime (Fin.last H.eventCount)) ∧
      F.1.eventCount = H.eventCount ∧
      F.1.horizon = H.time (Fin.last H.eventCount) ∧
      0 < F.1.horizon ∧ F.1.horizon ≤ H.horizon ∧
      IsEmpty (F.1.stage (Fin.last F.1.eventCount)).Carrier := by
  let hn := H.eventCount_pos_of_final_empty
  refine ⟨H.toFiniteHistory hn, rfl, H.toFiniteHistory_eventCount hn, rfl,
    H.last_time_pos hn, H.time_le_horizon, ?_⟩
  rw [H.toFiniteHistory_finalStage hn]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_finiteHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_finiteHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_finiteHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_finiteHistory

end ObservedHistory

namespace InitialIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}



theorem initial_nonempty (A : InitialIdentification P g H) [Nonempty P.Carrier] :
    Nonempty (H.stage 0).Carrier := Nonempty.map A.map inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.initial_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.initial_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.initial_nonempty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.initial_nonempty


def toFiniteHistory (A : InitialIdentification P g H) (hn : 0 < H.eventCount) :
    InitialIdentification P g (H.toFiniteHistory hn).1 := A.restrict _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory


@[simp] theorem toFiniteHistory_map (A : InitialIdentification P g H)
    (hn : 0 < H.eventCount) : (A.toFiniteHistory hn).map = A.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_map


theorem toFiniteHistory_isPrefixOf (A : InitialIdentification P g H)
    (hn : 0 < H.eventCount) : (A.toFiniteHistory hn).IsPrefixOf A :=
  A.restrict_isPrefixOf _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_isPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_isPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_isPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.toFiniteHistory_isPrefixOf

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
