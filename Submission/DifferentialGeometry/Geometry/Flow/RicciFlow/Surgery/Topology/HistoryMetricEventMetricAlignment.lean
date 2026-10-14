import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryMetricEvent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem heq_retainedCoreEvent_incoming_metric
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : RetainedCoreEvent P Q a s} {F : RetainedCoreEvent P' Q' a' s'}
    (h : HEq E F) (t : ℝ) :
    HEq (E.incoming.flow.base.metric t) (F.incoming.flow.base.metric t) := by
  cases hP
  cases hQ
  cases ha
  cases hs
  have hEq : E = F := eq_of_heq h
  cases hEq
  exact HEq.rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.heq_retainedCoreEvent_incoming_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.heq_retainedCoreEvent_incoming_metric target :: scope.openDecls } }

private theorem heq_retainedCoreEvent_outputMetric
    {P Q P' Q' : OrientedThreeStage.{u}} {a s a' s' : ℝ}
    (hP : P = P') (hQ : Q = Q') (ha : a = a') (hs : s = s')
    {E : RetainedCoreEvent P Q a s} {F : RetainedCoreEvent P' Q' a' s'}
    (h : HEq E F) : HEq E.outputMetric F.outputMetric := by
  cases hP
  cases hQ
  cases ha
  cases hs
  have hEq : E = F := eq_of_heq h
  cases hEq
  exact HEq.rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.heq_retainedCoreEvent_outputMetric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.heq_retainedCoreEvent_outputMetric target :: scope.openDecls } }

namespace RetainedCoreHistory

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem exists_extension_after_metricCutCapEvent_preserving_debit_with_metric_alignment
    (H : RetainedCoreHistory P) (A : InitialIdentification P g H.toHistory)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {Q : OrientedThreeStage.{u}} {s : ℝ}
    (E : MetricCutCapEvent (H.stage (Fin.last H.eventCount)) Q
      (H.time (Fin.last H.eventCount)) s)
    (hOld : E.old = E.transition.trace.retainedCore)
    (hinit : E.incoming.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (v : ℝ) (F : Set E.incoming.terminalRegularOpen) (hF : IsCompact F)
    (hdebit : riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric _root_.Set.univ +
      ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen E.terminal.metric F)
    (hcurvature : ∀ b : ℝ, 0 < b →
      (∀ x, InFixedHamiltonIveyRegion E.terminal.metric b x) →
      ∀ x, InFixedHamiltonIveyRegion E.outputMetric b x)
    (hscalar : ∀ B : ℝ, B ≤ 0 →
      (∀ x, B ≤ metricScalarAt E.terminal.metric x) →
      ∀ x, B ≤ metricScalarAt E.outputMetric x) :
    ∃ (K : RetainedCoreHistory P) (B : InitialIdentification P g K.toHistory)
      (i : Fin K.eventCount),
      A.IsPrefixOf B ∧ s < K.horizon ∧ K.eventCount = H.eventCount + 1 ∧
      K.time (Fin.last K.eventCount) = s ∧ K.stage (Fin.last K.eventCount) = Q ∧
      HEq (K.initialMetric (Fin.last K.eventCount)) E.outputMetric ∧
      i.val = H.eventCount ∧
      K.stage i.castSucc = H.stage (Fin.last H.eventCount) ∧
      K.time i.castSucc = H.time (Fin.last H.eventCount) ∧
      K.stage i.succ = Q ∧ K.time i.succ = s ∧
      HEq (K.coreEvent i) (E.toRetainedCoreEvent hOld) ∧
      HEq (K.initialMetric i.castSucc)
        (E.incoming.flow.base.metric (H.time (Fin.last H.eventCount))) ∧
      HEq (K.initialMetric i.succ) E.outputMetric ∧
      ∃ F' : Set (K.coreEvent i).incoming.terminalRegularOpen,
        HEq F' F ∧ IsCompact F' ∧
        riemannianVolumeMeasure ThreeModel (K.stage i.succ).Carrier
            (K.coreEvent i).outputMetric _root_.Set.univ +
          ENNReal.ofReal ((Nat.card (K.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
        riemannianVolumeMeasure ThreeModel (K.coreEvent i).incoming.terminalRegularOpen
            (K.coreEvent i).terminal.metric F' ∧
        (∀ b : ℝ, 0 < b →
          (∀ x, InFixedHamiltonIveyRegion (K.coreEvent i).terminal.metric b x) →
          ∀ x, InFixedHamiltonIveyRegion (K.coreEvent i).outputMetric b x) ∧
        (∀ B₀ : ℝ, B₀ ≤ 0 →
          (∀ x, B₀ ≤ metricScalarAt (K.coreEvent i).terminal.metric x) →
          ∀ x, B₀ ≤ metricScalarAt (K.coreEvent i).outputMetric x) := by
  obtain ⟨K, B, hprefix, hhorizon, hcount, hend, hstage, hmetric,
    i, hi, hP, ha, hQ, hs, hE, hdebit'⟩ :=
    H.exists_extension_after_metricCutCapEvent_preserving_debit A htime E hOld hinit
      v F hF hdebit hcurvature hscalar
  refine ⟨K, B, i, hprefix, hhorizon, hcount, hend, hstage, hmetric,
    hi, hP, ha, hQ, hs, hE, ?_, ?_, hdebit'⟩
  · let D := E.toRetainedCoreEvent hOld
    have hsrcKD : HEq
        ((K.coreEvent i).incoming.flow.base.metric (K.time i.castSucc))
        (D.incoming.flow.base.metric (K.time i.castSucc)) :=
      heq_retainedCoreEvent_incoming_metric hP hQ ha hs hE _
    have hsrcTime : HEq
        (D.incoming.flow.base.metric (K.time i.castSucc))
        (D.incoming.flow.base.metric (H.time (Fin.last H.eventCount))) :=
      heq_of_eq (congrArg (fun t : ℝ => D.incoming.flow.base.metric t) ha)
    have hsrc' : HEq
        ((K.coreEvent i).incoming.flow.base.metric (K.time i.castSucc))
        (E.incoming.flow.base.metric (H.time (Fin.last H.eventCount))) := by
      exact hsrcKD.trans (hsrcTime.trans HEq.rfl)
    have hsrcK : (K.coreEvent i).incoming.flow.base.metric (K.time i.castSucc) =
        K.initialMetric i.castSucc := K.event_initial i
    exact (heq_of_eq hsrcK.symm).trans hsrc'
  · have hout' : HEq (K.coreEvent i).outputMetric E.outputMetric :=
      heq_retainedCoreEvent_outputMetric hP hQ ha hs hE
    have houtK : (K.coreEvent i).outputMetric = K.initialMetric i.succ :=
      K.event_output i
    exact (heq_of_eq houtK.symm).trans hout'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_debit_with_metric_alignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_debit_with_metric_alignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_debit_with_metric_alignment ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_after_metricCutCapEvent_preserving_debit_with_metric_alignment


end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
