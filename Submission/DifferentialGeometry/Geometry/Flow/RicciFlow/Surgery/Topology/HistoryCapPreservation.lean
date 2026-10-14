import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MetricCutCapScalarLower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreMetricEvent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerBookkeeping
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalTraceConstruction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u

namespace SamePresentation

variable {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
  {E : MetricCutCapEvent P Q a s} {F : MetricCutCapEvent P' Q' a' s'}

theorem cap_scalar_lower_iff (R : E.SamePresentation F) (B : ℝ) :
    (∀ q ∈ E.capRegion, B ≤ metricScalarAt E.outputMetric q) ↔
      ∀ q ∈ F.capRegion, B ≤ metricScalarAt F.outputMetric q := by
  cases R.incomingStage_eq
  cases R.outgoingStage_eq
  cases R.leftTime_eq
  cases R.eventTime_eq
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq R.outputMetric_heq
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.cap_scalar_lower_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.cap_scalar_lower_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.cap_scalar_lower_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.cap_scalar_lower_iff

theorem old_eq_retainedCore_iff (R : E.SamePresentation F) :
    E.old = E.transition.trace.retainedCore ↔ F.old = F.transition.trace.retainedCore := by
  cases R.incomingStage_eq
  cases R.outgoingStage_eq
  cases R.leftTime_eq
  cases R.eventTime_eq
  cases E
  cases F
  cases R.discarded_eq
  cases R.capped_eq
  cases eq_of_heq R.transition_heq
  cases eq_of_heq R.old_heq
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.old_eq_retainedCore_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.old_eq_retainedCore_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.old_eq_retainedCore_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.SamePresentation.old_eq_retainedCore_iff

end SamePresentation

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem cap_scalar_lower_bound_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' B : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s)
    (hcap : ∀ x ∈ E.capRegion, B ≤ metricScalarAt E.outputMetric x) :
    ∀ x ∈ (MetricCutCapEvent.transport hP hQ ha hs E).capRegion,
      B ≤ metricScalarAt (MetricCutCapEvent.transport hP hQ ha hs E).outputMetric x := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact hcap

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cap_scalar_lower_bound_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.cap_scalar_lower_bound_transport target :: scope.openDecls } }

private theorem old_eq_retainedCore_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s) (hOld : E.old = E.transition.trace.retainedCore) :
    (MetricCutCapEvent.transport hP hQ ha hs E).old =
      (MetricCutCapEvent.transport hP hQ ha hs E).transition.trace.retainedCore := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact hOld

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.old_eq_retainedCore_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.old_eq_retainedCore_transport target :: scope.openDecls } }

private theorem retainedCoreEvent_heq_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s) :
    HEq (RetainedCoreEvent.transport hP hQ ha hs E) E := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact HEq.rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.retainedCoreEvent_heq_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.retainedCoreEvent_heq_transport target :: scope.openDecls } }

namespace ObservedHistory

variable (H : ObservedHistory.{u}) {Q : OrientedThreeStage.{u}} {s : ℝ}
  (hs : H.time (Fin.last H.eventCount) < s)
  (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
    (H.time (Fin.last H.eventCount)) s)
  (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount))

theorem appendEvent_event_castSucc_heq (j : Fin H.eventCount) :
    HEq ((H.appendEvent hs E hinit).event j.castSucc) (H.event j) := by
  rw [H.appendEvent_event_apply, H.extendEventFamily_castSucc]
  exact MetricCutCapEvent.heq_transport _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_heq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_heq

theorem appendEvent_event_last_heq :
    HEq ((H.appendEvent hs E hinit).event (Fin.last H.eventCount)) E := by
  rw [H.appendEvent_event_last]
  exact MetricCutCapEvent.heq_transport _ _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_heq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_heq

theorem appendEvent_event_castSucc_samePresentation (j : Fin H.eventCount) :
    ((H.appendEvent hs E hinit).event j.castSucc).SamePresentation (H.event j) := by
  apply MetricCutCapEvent.SamePresentation.of_heq_of_eq
    (H.appendEvent_stage_castSucc hs E hinit j.castSucc)
    (H.appendEvent_stage_castSucc hs E hinit j.succ)
    (H.appendEvent_time_castSucc hs E hinit j.castSucc)
    (H.appendEvent_time_castSucc hs E hinit j.succ)
  exact H.appendEvent_event_castSucc_heq hs E hinit j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_samePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_samePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_samePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_castSucc_samePresentation

theorem appendEvent_event_last_samePresentation :
    ((H.appendEvent hs E hinit).event (Fin.last H.eventCount)).SamePresentation E := by
  apply MetricCutCapEvent.SamePresentation.of_heq_of_eq
    (H.appendEvent_stage_castSucc hs E hinit (Fin.last H.eventCount))
    (H.extendStage_last Q E.outputMetric)
    (H.appendEvent_time_castSucc hs E hinit (Fin.last H.eventCount))
    (H.appendEvent_time_last hs E hinit)
  exact H.appendEvent_event_last_heq hs E hinit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_samePresentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_samePresentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_samePresentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_event_last_samePresentation

theorem appendEvent_isPrefixOf_of_time_eq_horizon
    (htime : H.time (Fin.last H.eventCount) = H.horizon) :
    H.IsPrefixOf (H.appendEvent hs E hinit) := by
  apply H.appendEvent_isPrefixOf hs E hinit (htime ▸ hs)
  intro h
  exact (ne_of_lt h htime).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_isPrefixOf_of_time_eq_horizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_isPrefixOf_of_time_eq_horizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_isPrefixOf_of_time_eq_horizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_isPrefixOf_of_time_eq_horizon

theorem appendEvent_cap_scalar_lower_bound
    {c b B : ℝ}
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ _root_.Set.Ioc c b →
      ∀ x ∈ (H.event j).capRegion, B ≤ metricScalarAt (H.event j).outputMetric x)
    (hE : s ∈ _root_.Set.Ioc c b → ∀ x ∈ E.capRegion, B ≤ metricScalarAt E.outputMetric x) :
    ∀ j : Fin (H.appendEvent hs E hinit).eventCount,
      (H.appendEvent hs E hinit).time j.succ ∈ _root_.Set.Ioc c b →
      ∀ x ∈ ((H.appendEvent hs E hinit).event j).capRegion,
        B ≤ metricScalarAt ((H.appendEvent hs E hinit).event j).outputMetric x := by
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · intro ht
    have hcs : s ∈ _root_.Set.Ioc c b := by
      change (H.appendEvent hs E hinit).time (Fin.last (H.eventCount + 1)) ∈ _root_.Set.Ioc c b at ht
      rwa [H.appendEvent_time_last] at ht
    rw [H.appendEvent_event_last]
    exact cap_scalar_lower_bound_transport _ _ _ _ E (hE hcs)
  · intro ht
    have hck : H.time k.succ ∈ _root_.Set.Ioc c b := by
      change (H.appendEvent hs E hinit).time k.succ.castSucc ∈ _root_.Set.Ioc c b at ht
      rwa [H.appendEvent_time_castSucc] at ht
    rw [H.appendEvent_event_apply, H.extendEventFamily_castSucc]
    exact cap_scalar_lower_bound_transport _ _ _ _ (H.event k) (hcap k hck)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_cap_scalar_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_cap_scalar_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_cap_scalar_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_cap_scalar_lower_bound

theorem appendEvent_old_eq_retainedCore
    {c b : ℝ}
    (hOld : ∀ j : Fin H.eventCount, H.time j.succ ∈ _root_.Set.Ioc c b →
      (H.event j).old = (H.event j).transition.trace.retainedCore)
    (hE : s ∈ _root_.Set.Ioc c b → E.old = E.transition.trace.retainedCore) :
    ∀ j : Fin (H.appendEvent hs E hinit).eventCount,
      (H.appendEvent hs E hinit).time j.succ ∈ _root_.Set.Ioc c b →
      ((H.appendEvent hs E hinit).event j).old =
        ((H.appendEvent hs E hinit).event j).transition.trace.retainedCore := by
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · intro ht
    have hcs : s ∈ _root_.Set.Ioc c b := by
      change (H.appendEvent hs E hinit).time (Fin.last (H.eventCount + 1)) ∈ _root_.Set.Ioc c b at ht
      rwa [H.appendEvent_time_last] at ht
    rw [H.appendEvent_event_last]
    exact old_eq_retainedCore_transport _ _ _ _ E (hE hcs)
  · intro ht
    have hck : H.time k.succ ∈ _root_.Set.Ioc c b := by
      change (H.appendEvent hs E hinit).time k.succ.castSucc ∈ _root_.Set.Ioc c b at ht
      rwa [H.appendEvent_time_castSucc] at ht
    rw [H.appendEvent_event_apply, H.extendEventFamily_castSucc]
    exact old_eq_retainedCore_transport _ _ _ _ (H.event k) (hOld k hck)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_old_eq_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_old_eq_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_old_eq_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.appendEvent_old_eq_retainedCore

end ObservedHistory

namespace RetainedCoreHistory

variable {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P)
  {Q : OrientedThreeStage.{u}} {s : ℝ}
  (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
    (H.time (Fin.last H.eventCount)) s)
  (hOld : E.old = E.transition.trace.retainedCore)
  (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount))

theorem appendMetricCutCapEvent_isPrefixOf
    (htime : H.time (Fin.last H.eventCount) = H.horizon) :
    H.toHistory.IsPrefixOf
      (H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory :=
  H.appendEvent_isPrefixOf E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    (htime ▸ E.incoming.lt)
    (H.appendEventCompatible_of_time_eq_horizon (E.toRetainedCoreEvent hOld) htime)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_isPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_isPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_isPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_isPrefixOf

theorem appendMetricCutCapEvent_cap_scalar_lower_bound
    {c b B : ℝ}
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ _root_.Set.Ioc c b →
      ∀ x ∈ (H.toHistory.event j).capRegion,
        B ≤ metricScalarAt (H.toHistory.event j).outputMetric x)
    (hE : s ∈ _root_.Set.Ioc c b → ∀ x ∈ E.capRegion, B ≤ metricScalarAt E.outputMetric x) :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    ∀ j : Fin K.eventCount, K.time j.succ ∈ _root_.Set.Ioc c b →
      ∀ x ∈ (K.toHistory.event j).capRegion,
        B ≤ metricScalarAt (K.toHistory.event j).outputMetric x := by
  intro K
  have h := H.toHistory.appendEvent_cap_scalar_lower_bound E.incoming.lt
    (E.toRetainedCoreEvent hOld).toMetricCutCapEvent hinit hcap hE
  intro j hj
  have hsame := H.appendEvent_toHistory_samePresentation E.incoming.lt
    (E.toRetainedCoreEvent hOld) hinit
  exact ((hsame.event_eq j).cap_scalar_lower_iff B).mpr (h _ hj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_cap_scalar_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_cap_scalar_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_cap_scalar_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_cap_scalar_lower_bound

theorem appendMetricCutCapEvent_old_eq_retainedCore :
    let K := H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit
    ∀ j : Fin K.eventCount,
      (K.toHistory.event j).old = (K.toHistory.event j).transition.trace.retainedCore := by
  intro K j
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_old_eq_retainedCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_old_eq_retainedCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_old_eq_retainedCore ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendMetricCutCapEvent_old_eq_retainedCore

theorem exists_extension_after_metricCutCapEvent_preserving_cap_scalar_lower_bound
    (htime : H.time (Fin.last H.eventCount) = H.horizon) {c b B : ℝ}
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ _root_.Set.Ioc c b →
      ∀ x ∈ (H.toHistory.event j).capRegion,
        B ≤ metricScalarAt (H.toHistory.event j).outputMetric x)
    (hE : s ∈ _root_.Set.Ioc c b → ∀ x ∈ E.capRegion, B ≤ metricScalarAt E.outputMetric x) :
    ∃ K : RetainedCoreHistory P,
      (H.appendEvent E.incoming.lt (E.toRetainedCoreEvent hOld) hinit).toHistory.IsPrefixOf
        K.toHistory ∧ H.toHistory.IsPrefixOf K.toHistory ∧
      s < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
      (∀ j : Fin K.eventCount, K.time j.succ ∈ _root_.Set.Ioc c b →
        ∀ x ∈ (K.toHistory.event j).capRegion,
          B ≤ metricScalarAt (K.toHistory.event j).outputMetric x) ∧
      (∀ j : Fin K.eventCount,
        (K.toHistory.event j).old = (K.toHistory.event j).transition.trace.retainedCore) ∧
      ∃ j : Fin K.eventCount, j.val = H.eventCount ∧
        K.stage j.castSucc = H.stage (Fin.last H.eventCount) ∧
        K.time j.castSucc = H.time (Fin.last H.eventCount) ∧
        K.stage j.succ = Q ∧ K.time j.succ = s ∧
        HEq (K.coreEvent j) (E.toRetainedCoreEvent hOld) := by
  let F := E.toRetainedCoreEvent hOld
  have hinitF : F.toMetricCutCapEvent.incoming.flow.base.metric
      (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount) := hinit
  let J := H.appendEvent E.incoming.lt F hinitF
  have hJs : J.time (Fin.last J.eventCount) = s := H.appendEvent_time_last E.incoming.lt F hinit
  have hJtime : J.time (Fin.last J.eventCount) = J.horizon := hJs
  obtain ⟨T, hsT, S, hS⟩ := exists_closedSlab_of_metric
    (J.stage (Fin.last J.eventCount)) (J.initialMetric (Fin.last J.eventCount))
    (J.time (Fin.last J.eventCount))
  let K := J.extendHorizon T (hJtime ▸ hsT.le) S hS
  have hprefix : J.toHistory.IsPrefixOf K.toHistory :=
    J.extendHorizon_isPrefixOf_of_time_eq_horizon T (hJtime ▸ hsT.le) S hS hJtime
  have hcapK := H.appendMetricCutCapEvent_cap_scalar_lower_bound E hOld hinit hcap hE
  refine ⟨K,hprefix,(H.appendMetricCutCapEvent_isPrefixOf E hOld hinit htime).trans hprefix,
    hJs ▸ hsT,rfl,hcapK,?_,Fin.last H.eventCount,rfl,?_,?_,?_,?_,?_⟩
  · intro j
    rfl
  · exact H.appendEvent_stage_castSucc E.incoming.lt F hinit (Fin.last H.eventCount)
  · exact H.appendEvent_time_castSucc E.incoming.lt F hinit (Fin.last H.eventCount)
  · exact H.appendEvent_stage_last E.incoming.lt F hinit
  · exact H.appendEvent_time_last E.incoming.lt F hinit
  · change HEq ((H.appendEvent E.incoming.lt F hinitF).coreEvent (Fin.last H.eventCount)) F
    rw [H.appendEvent_coreEvent_last]
    unfold extendCoreEventLast
    exact retainedCoreEvent_heq_transport _ _ _ _ F

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_cap_scalar_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_cap_scalar_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_cap_scalar_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_cap_scalar_lower_bound

omit E hOld hinit in
theorem exists_backwardPointTrace_on_time_window
    (i first : Fin H.eventCount) (hle : first.castSucc ≤ i.castSucc)
    (x : (H.toHistory.event i).incoming.terminalRegularOpen) {q Qend Qcap c b : ℝ} {C : ℝ≥0}
    (hq : 0 < q) (hqend : q ≤ Qend) (hendcap : Qend < Qcap)
    (hscalar : metricScalarAt (H.toHistory.event i).terminal.metric x ≤ Qend)
    (hc : c ∈ _root_.Set.Ico (H.time first.castSucc) (H.time first.succ))
    (htime : C * (H.time i.succ - c) ≤ Qend⁻¹ - Qcap⁻¹)
    (hib : H.time i.castSucc ≤ b)
    (hderiv : ∀ j : Fin H.eventCount, first.castSucc ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ y : (H.stage j.castSucc).Carrier, ∀ t ∈ _root_.Set.Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.toHistory.event j).incoming.flow.scalar t y →
      |derivWithin (fun v => (H.toHistory.event j).incoming.flow.scalar v y) (_root_.Set.Iic t) t| ≤
        C * (H.toHistory.event j).incoming.flow.scalar t y ^ 2)
    (hcap : ∀ j : Fin H.eventCount, H.time j.succ ∈ _root_.Set.Ioc c b →
      ∀ y ∈ (H.toHistory.event j).capRegion,
        Qcap ≤ metricScalarAt (H.toHistory.event j).outputMetric y) :
    ∃ A : BackwardPointTrace H.toHistory first.castSucc i.castSucc hle x.val,
      ∀ (j : Fin H.eventCount) (hf : first.castSucc ≤ j.castSucc)
        (hl : j.castSucc ≤ i.castSucc),
        ∀ t ∈ _root_.Set.Ico (H.time j.castSucc) (H.time j.succ), c ≤ t →
          (H.toHistory.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ Qcap := by
  apply H.toHistory.exists_backwardPointTrace_to_terminal_on_time_window
    i first hle x hq hqend hendcap hscalar hc htime hderiv
  · intro j hf hl
    rfl
  · intro j hf hl boundary z y hpres
    apply hcap j _ y ⟨boundary.val, z, hpres⟩
    exact ⟨hc.2.trans_le (H.time_strictMono.monotone
      (by change first.val + 1 ≤ j.val + 1; exact Nat.succ_le_succ hf)),
      (H.time_strictMono.monotone hl).trans hib⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardPointTrace_on_time_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardPointTrace_on_time_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardPointTrace_on_time_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_backwardPointTrace_on_time_window

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end

noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

private theorem frame_and_discard_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : MetricCutCapEvent P Q a s)
    (hbfr : E.transition.boundaryFrameReversing)
    (hctrl : E.poincareStandardDiscarded) :
    (MetricCutCapEvent.transport hP hQ ha hs E).transition.boundaryFrameReversing ∧
      (MetricCutCapEvent.transport hP hQ ha hs E).poincareStandardDiscarded := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact ⟨hbfr, hctrl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frame_and_discard_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.frame_and_discard_transport target :: scope.openDecls } }

theorem RetainedCoreHistory.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    (hbfrE : E.transition.boundaryFrameReversing)
    (hctrlE : E.toMetricCutCapEvent.poincareStandardDiscarded) :
    ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
      ((H.appendEvent hs E hinit).coreEvent i).transition.boundaryFrameReversing ∧
      ((H.appendEvent hs E hinit).coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded := by
  change ∀ i : Fin (H.eventCount + 1), _
  intro i
  change (H.extendCoreEventFamily E i).toMetricCutCapEvent.transition.boundaryFrameReversing ∧
    (H.extendCoreEventFamily E i).toMetricCutCapEvent.poincareStandardDiscarded
  rw [H.extendCoreEventFamily_toMetricCutCapEvent]
  cases i using Fin.lastCases with
  | cast i =>
    rw [ObservedHistory.extendEventFamily_castSucc]
    exact frame_and_discard_transport _ _ _ _ _ (hbfr i) (hctrl i)
  | last =>
    rw [ObservedHistory.extendEventFamily_last]
    exact frame_and_discard_transport _ _ _ _ _ hbfrE hctrlE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem scalar_time_derivative_bound_transport
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' q C : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    (E : RetainedCoreEvent P Q a s)
    (hbound : ∀ t ∈ _root_.Set.Ioo a s, ∀ x : P.Carrier, q < E.incoming.flow.scalar t x →
      |derivWithin (fun v => E.incoming.flow.scalar v x) (_root_.Set.Iic t) t| ≤
        C * E.incoming.flow.scalar t x ^ 2) :
    ∀ t ∈ _root_.Set.Ioo a' s', ∀ x : P'.Carrier,
      q < (RetainedCoreEvent.transport hP hQ ha hs E).incoming.flow.scalar t x →
      |derivWithin (fun v => (RetainedCoreEvent.transport hP hQ ha hs E).incoming.flow.scalar v x)
        (_root_.Set.Iic t) t| ≤ C * (RetainedCoreEvent.transport hP hQ ha hs E).incoming.flow.scalar t x ^ 2 := by
  cases hP
  cases hQ
  cases ha
  cases hs
  exact hbound

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scalar_time_derivative_bound_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scalar_time_derivative_bound_transport target :: scope.openDecls } }

theorem RetainedCoreHistory.appendEvent_scalar_time_derivative_bound
    {P Q : OrientedThreeStage.{u}} (H : RetainedCoreHistory P) {s : ℝ}
    (hs : H.time (Fin.last H.eventCount) < s)
    (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {q C : ℝ}
    (hbound : ∀ i : Fin H.eventCount, ∀ t ∈ _root_.Set.Ioo (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier, q < (H.coreEvent i).incoming.flow.scalar t x →
        |derivWithin (fun v => (H.coreEvent i).incoming.flow.scalar v x) (_root_.Set.Iic t) t| ≤
          C * (H.coreEvent i).incoming.flow.scalar t x ^ 2)
    (hE : ∀ t ∈ _root_.Set.Ioo (H.time (Fin.last H.eventCount)) s,
      ∀ x : (H.stage (Fin.last H.eventCount)).Carrier, q < E.incoming.flow.scalar t x →
        |derivWithin (fun v => E.incoming.flow.scalar v x) (_root_.Set.Iic t) t| ≤
          C * E.incoming.flow.scalar t x ^ 2) :
    ∀ i : Fin (H.appendEvent hs E hinit).eventCount,
      ∀ t ∈ _root_.Set.Ioo ((H.appendEvent hs E hinit).time i.castSucc) ((H.appendEvent hs E hinit).time i.succ),
      ∀ x : ((H.appendEvent hs E hinit).stage i.castSucc).Carrier,
        q < ((H.appendEvent hs E hinit).coreEvent i).incoming.flow.scalar t x →
        |derivWithin (fun v => ((H.appendEvent hs E hinit).coreEvent i).incoming.flow.scalar v x)
          (_root_.Set.Iic t) t| ≤ C * ((H.appendEvent hs E hinit).coreEvent i).incoming.flow.scalar t x ^ 2 := by
  change ∀ i : Fin (H.eventCount + 1), _
  intro i
  cases i using Fin.lastCases with
  | cast i =>
    rw [H.appendEvent_coreEvent_castSucc]
    exact scalar_time_derivative_bound_transport _ _ _ _ _ (hbound i)
  | last =>
    rw [H.appendEvent_coreEvent_last]
    exact scalar_time_derivative_bound_transport _ _ _ _ _ hE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_scalar_time_derivative_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_scalar_time_derivative_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_scalar_time_derivative_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.appendEvent_scalar_time_derivative_bound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
