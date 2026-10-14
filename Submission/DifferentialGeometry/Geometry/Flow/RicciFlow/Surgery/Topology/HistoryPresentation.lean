import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

structure SamePresentation
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (E : MetricCutCapEvent P Q a s) (F : MetricCutCapEvent P' Q' a' s') : Prop where
  incomingStage_eq : P = P'
  outgoingStage_eq : Q = Q'
  leftTime_eq : a = a'
  eventTime_eq : s = s'
  discarded_eq : E.discarded = F.discarded
  capped_eq : E.capped = F.capped
  transition_heq : HEq E.transition F.transition
  incomingMetric_heq : ∀ t ∈ _root_.Set.Ico a s,
    HEq (E.incoming.flow.base.metric t) (F.incoming.flow.base.metric t)
  terminalRegion_heq : HEq E.incoming.terminalRegularOpen F.incoming.terminalRegularOpen
  terminalMetric_heq : HEq E.terminal.metric F.terminal.metric
  outputMetric_heq : HEq E.outputMetric F.outputMetric
  old_heq : HEq E.old F.old
  oldCharts_heq : HEq E.oldCharts F.oldCharts
  oldTerminal_heq : HEq E.oldTerminal F.oldTerminal
  oldOutput_heq : HEq E.oldOutput F.oldOutput

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation

@[refl] theorem SamePresentation.refl
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s) :
    E.SamePresentation E where
  incomingStage_eq := rfl
  outgoingStage_eq := rfl
  leftTime_eq := rfl
  eventTime_eq := rfl
  discarded_eq := rfl
  capped_eq := rfl
  transition_heq := HEq.rfl
  incomingMetric_heq _ _ := HEq.rfl
  terminalRegion_heq := HEq.rfl
  terminalMetric_heq := HEq.rfl
  outputMetric_heq := HEq.rfl
  old_heq := HEq.rfl
  oldCharts_heq := HEq.rfl
  oldTerminal_heq := HEq.rfl
  oldOutput_heq := HEq.rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.refl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.refl

@[symm] theorem SamePresentation.symm
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    (R : E.SamePresentation F) : F.SamePresentation E where
  incomingStage_eq := R.incomingStage_eq.symm
  outgoingStage_eq := R.outgoingStage_eq.symm
  leftTime_eq := R.leftTime_eq.symm
  eventTime_eq := R.eventTime_eq.symm
  discarded_eq := R.discarded_eq.symm
  capped_eq := R.capped_eq.symm
  transition_heq := R.transition_heq.symm
  incomingMetric_heq t ht := (R.incomingMetric_heq t
    (by simpa only [R.leftTime_eq, R.eventTime_eq] using ht)).symm
  terminalRegion_heq := R.terminalRegion_heq.symm
  terminalMetric_heq := R.terminalMetric_heq.symm
  outputMetric_heq := R.outputMetric_heq.symm
  old_heq := R.old_heq.symm
  oldCharts_heq := R.oldCharts_heq.symm
  oldTerminal_heq := R.oldTerminal_heq.symm
  oldOutput_heq := R.oldOutput_heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.symm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.symm

@[trans] theorem SamePresentation.trans
    {P Q P' Q' P'' Q'' : OrientedThreeStage.{u}} {a s a' s' a'' s'' : ℝ}
    {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}
    {G : MetricCutCapEvent P'' Q'' a'' s''}
    (R : E.SamePresentation F) (S : F.SamePresentation G) : E.SamePresentation G where
  incomingStage_eq := R.incomingStage_eq.trans S.incomingStage_eq
  outgoingStage_eq := R.outgoingStage_eq.trans S.outgoingStage_eq
  leftTime_eq := R.leftTime_eq.trans S.leftTime_eq
  eventTime_eq := R.eventTime_eq.trans S.eventTime_eq
  discarded_eq := R.discarded_eq.trans S.discarded_eq
  capped_eq := R.capped_eq.trans S.capped_eq
  transition_heq := R.transition_heq.trans S.transition_heq
  incomingMetric_heq t ht := (R.incomingMetric_heq t ht).trans
    (S.incomingMetric_heq t (by simpa only [← R.leftTime_eq, ← R.eventTime_eq] using ht))
  terminalRegion_heq := R.terminalRegion_heq.trans S.terminalRegion_heq
  terminalMetric_heq := R.terminalMetric_heq.trans S.terminalMetric_heq
  outputMetric_heq := R.outputMetric_heq.trans S.outputMetric_heq
  old_heq := R.old_heq.trans S.old_heq
  oldCharts_heq := R.oldCharts_heq.trans S.oldCharts_heq
  oldTerminal_heq := R.oldTerminal_heq.trans S.oldTerminal_heq
  oldOutput_heq := R.oldOutput_heq.trans S.oldOutput_heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.trans ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.trans

end MetricCutCapEvent

namespace ObservedHistory

structure SamePresentation (H K : ObservedHistory.{u}) : Prop where
  horizon_eq : H.horizon = K.horizon
  count_eq : H.eventCount = K.eventCount
  time_eq : ∀ j : Fin (H.eventCount + 1),
    H.time j = K.time (Fin.cast (congrArg (· + 1) count_eq) j)
  stage_eq : ∀ j : Fin (H.eventCount + 1),
    H.stage j = K.stage (Fin.cast (congrArg (· + 1) count_eq) j)
  initialMetric_heq : ∀ j : Fin (H.eventCount + 1),
    HEq (H.initialMetric j) (K.initialMetric (Fin.cast (congrArg (· + 1) count_eq) j))
  event_eq : ∀ i : Fin H.eventCount,
    (H.event i).SamePresentation (K.event (Fin.cast count_eq i))
  metric_heq : ∀ j : Fin (H.eventCount + 1), ∀ t ∈ H.stageDomain j,
    HEq (H.stageMetric j t) (K.stageMetric (Fin.cast (congrArg (· + 1) count_eq) j) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation

@[refl] theorem SamePresentation.refl (H : ObservedHistory.{u}) : H.SamePresentation H where
  horizon_eq := rfl
  count_eq := rfl
  time_eq _ := rfl
  stage_eq _ := rfl
  initialMetric_heq _ := HEq.rfl
  event_eq i := MetricCutCapEvent.SamePresentation.refl (H.event i)
  metric_heq _ _ _ := HEq.rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.refl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.refl


theorem SamePresentation.stageDomain_eq {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) (j : Fin (H.eventCount + 1)) :
    H.stageDomain j = K.stageDomain (Fin.cast (congrArg (· + 1) R.count_eq) j) := by
  cases j using Fin.lastCases with
  | last =>
    have hj : Fin.cast (congrArg (· + 1) R.count_eq) (Fin.last H.eventCount) =
        Fin.last K.eventCount := Fin.ext R.count_eq
    have ht := R.time_eq (Fin.last H.eventCount)
    rw [hj] at ht ⊢
    simp only [stageDomain, Fin.lastCases_last]
    exact congrArg₂ _root_.Set.Icc ht R.horizon_eq
  | cast i =>
    have hj : Fin.cast (congrArg (· + 1) R.count_eq) i.castSucc =
        (Fin.cast R.count_eq i).castSucc := Fin.ext rfl
    have hs : Fin.cast (congrArg (· + 1) R.count_eq) i.succ =
        (Fin.cast R.count_eq i).succ := Fin.ext rfl
    have ht := R.time_eq i.castSucc
    have hu := R.time_eq i.succ
    rw [hj] at ht ⊢
    rw [hs] at hu
    simp only [stageDomain, Fin.lastCases_castSucc]
    exact congrArg₂ _root_.Set.Ico ht hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageDomain_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageDomain_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageDomain_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageDomain_eq

@[symm] theorem SamePresentation.symm {H K : ObservedHistory.{u}}
    (R : H.SamePresentation K) : K.SamePresentation H := by
  let back : Fin (K.eventCount + 1) → Fin (H.eventCount + 1) :=
    Fin.cast (congrArg (· + 1) R.count_eq.symm)
  have hj (j : Fin (K.eventCount + 1)) :
      Fin.cast (congrArg (· + 1) R.count_eq) (back j) = j := Fin.ext rfl
  refine {
    horizon_eq := R.horizon_eq.symm
    count_eq := R.count_eq.symm
    time_eq := ?_
    stage_eq := ?_
    initialMetric_heq := ?_
    event_eq := ?_
    metric_heq := ?_ }
  · intro j
    simpa only [hj] using (R.time_eq (back j)).symm
  · intro j
    simpa only [hj] using (R.stage_eq (back j)).symm
  · intro j
    exact (hj j) ▸ (R.initialMetric_heq (back j)).symm
  · intro i
    have hi : Fin.cast R.count_eq (Fin.cast R.count_eq.symm i) = i := Fin.ext rfl
    exact hi ▸ (R.event_eq (Fin.cast R.count_eq.symm i)).symm
  · intro j t ht
    have hdom := R.stageDomain_eq (back j)
    rw [hj] at hdom
    have ht' : t ∈ H.stageDomain (back j) := by rw [hdom]; exact ht
    exact (hj j) ▸ (R.metric_heq (back j) t ht').symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.symm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.symm

@[trans] theorem SamePresentation.trans {H K L : ObservedHistory.{u}}
    (R : H.SamePresentation K) (S : K.SamePresentation L) : H.SamePresentation L := by
  have hj (j : Fin (H.eventCount + 1)) :
      Fin.cast (congrArg (· + 1) S.count_eq)
        (Fin.cast (congrArg (· + 1) R.count_eq) j) =
      Fin.cast (congrArg (· + 1) (R.count_eq.trans S.count_eq)) j := Fin.ext rfl
  refine {
    horizon_eq := R.horizon_eq.trans S.horizon_eq
    count_eq := R.count_eq.trans S.count_eq
    time_eq := ?_
    stage_eq := ?_
    initialMetric_heq := ?_
    event_eq := ?_
    metric_heq := ?_ }
  · intro j
    simpa only [hj] using (R.time_eq j).trans
      (S.time_eq (Fin.cast (congrArg (· + 1) R.count_eq) j))
  · intro j
    simpa only [hj] using (R.stage_eq j).trans
      (S.stage_eq (Fin.cast (congrArg (· + 1) R.count_eq) j))
  · intro j
    exact (hj j) ▸ (R.initialMetric_heq j).trans
      (S.initialMetric_heq (Fin.cast (congrArg (· + 1) R.count_eq) j))
  · intro i
    have hi : Fin.cast S.count_eq (Fin.cast R.count_eq i) =
        Fin.cast (R.count_eq.trans S.count_eq) i := Fin.ext rfl
    exact hi ▸ (R.event_eq i).trans (S.event_eq (Fin.cast R.count_eq i))
  · intro j t ht
    have ht' : t ∈ K.stageDomain (Fin.cast (congrArg (· + 1) R.count_eq) j) := by
      rw [← R.stageDomain_eq j]
      exact ht
    exact (hj j) ▸ (R.metric_heq j t ht).trans
      (S.metric_heq (Fin.cast (congrArg (· + 1) R.count_eq) j) t ht')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.trans ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.trans
end ObservedHistory
end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
