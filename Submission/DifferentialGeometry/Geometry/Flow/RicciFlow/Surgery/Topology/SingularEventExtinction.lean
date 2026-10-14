import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHorizonExtinction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCapPreservation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryMetricEvent
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffRecordEventExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionExistenceReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width
universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

private theorem prefix_stage_zero_eq {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    K.stage 0 = H.stage 0 := by
  have hh := h.presentation.stage_eq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_stage_zero] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.prefix_stage_zero_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.prefix_stage_zero_eq target :: scope.openDecls } }

private theorem prefix_metric_zero_heq {H K : ObservedHistory.{u}} (h : H.IsPrefixOf K) :
    HEq (K.initialMetric 0) (H.initialMetric 0) := by
  have hh := h.presentation.initialMetric_heq 0
  simpa only [Fin.cast_zero, ObservedHistory.restrict_initialMetric_zero,
    ObservedHistory.restrict_stage_zero] using hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.prefix_metric_zero_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.prefix_metric_zero_heq target :: scope.openDecls } }

theorem exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants
    (P : OrientedThreeStage.{u}) [SimplyConnectedSpace P.Carrier] (g : P.Metric)
    (hproduce : ∀ B : ℝ, 0 < B → ∃ (p₀ : CutoffParameters) (v : ℝ) (Inv : RetainedCoreHistory P → Prop),
      0 < v ∧ Inv (RetainedCoreHistory.atZero P g) ∧
      ∀ H : RetainedCoreHistory P, InitialIdentification P g H.toHistory → Inv H →
        ∀ p : CutoffParameters,
        H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
        p.fixed = p₀.fixed → p.modelRadius = p₀.modelRadius →
        p.modelOrder = p₀.modelOrder → p.modelAccuracy = p₀.modelAccuracy →
        p.recenterConstant = p₀.recenterConstant →
        (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) →
        (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) →
          (∀ i : Fin H.eventCount,
            (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                (H.coreEvent i).outputMetric _root_.Set.univ +
                  ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
        ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s), s ≤ B →
          G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
          ∃ (Q : OrientedThreeStage.{u})
            (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
              (H.time (Fin.last H.eventCount)) s)
            (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
              (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
            (q : CutoffParameters),
            E.incoming = G ∧ Inv (H.appendEvent E.incoming.lt E hinit) ∧
            q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
            q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
            q.recenterConstant = p.recenterConstant ∧
            Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q) ∧ E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric _root_.Set.univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  classical
  obtain ⟨c, hc, hscalar0⟩ := exists_initialScalarBarrier_of_compact g
  let B := _root_.Max.max 1 (extinctionThreshold c (canonicalWidth g P.orientation) + 1)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hthr : extinctionThreshold c (canonicalWidth g P.orientation) < B :=
    (lt_add_one _).trans_le (le_max_right _ _)
  obtain ⟨p₀, v, Inv, hv, hInv, hstep⟩ := hproduce B hB
  let H₀ := RetainedCoreHistory.atZero P g
  let S : Set (RetainedCoreHistory P) := {H |
    H₀.toHistory.IsPrefixOf H.toHistory ∧ H.horizon ≤ B ∧
    H.time (Fin.last H.eventCount) = H.horizon ∧ Inv H ∧
    ∃ p : CutoffParameters,
      p.fixed = p₀.fixed ∧ p.modelRadius = p₀.modelRadius ∧
      p.modelOrder = p₀.modelOrder ∧ p.modelAccuracy = p₀.modelAccuracy ∧
      p.recenterConstant = p₀.recenterConstant ∧
      Nonempty (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) ∧
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin H.eventCount,
        ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
            (H.coreEvent i).outputMetric _root_.Set.univ +
              ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
            (H.coreEvent i).terminal.metric F}
  have hzero : H₀ ∈ S := by
    refine ⟨ObservedHistory.IsPrefixOf.refl _, hB.le, rfl, hInv, p₀, rfl, rfl, rfl, rfl, rfl,
      ⟨fun i => Fin.elim0 i⟩, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  have hex : ∀ H ∈ S, ∃ p : CutoffParameters,
      p.fixed = p₀.fixed ∧ p.modelRadius = p₀.modelRadius ∧
      p.modelOrder = p₀.modelOrder ∧ p.modelAccuracy = p₀.modelAccuracy ∧
      p.recenterConstant = p₀.recenterConstant ∧
      Nonempty (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) ∧
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      ∀ i : Fin H.eventCount,
        ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
          riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
            (H.coreEvent i).outputMetric _root_.Set.univ +
              ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
          riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
            (H.coreEvent i).terminal.metric F := fun H hH => hH.2.2.2.2
  choose p hfixed hradius horder haccuracy hrecenter hrecords hbfr hctrl hdebit using hex
  have hclosed : ∀ H ∈ S, H.horizon < B →
      ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
        (H.time (Fin.last H.eventCount)) s), s ≤ B →
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
        ∃ (Q : OrientedThreeStage.{u})
          (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
            (H.time (Fin.last H.eventCount)) s)
          (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
            (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount)),
          E.incoming = G ∧ H.appendEvent E.incoming.lt E hinit ∈ S := by
    intro H hH hHB s G hs hinit hsing
    let A := (InitialIdentification.atZero P g).of_stageZero
      (prefix_stage_zero_eq hH.1) (prefix_metric_zero_heq hH.1)
    obtain ⟨Q, E, hE, q, hincoming, hInvNext, hqfixed, hqradius, hqorder, hqaccuracy, hqrecenter,
      ⟨R⟩, hbfrE, hctrlE, F, hF, hvol⟩ :=
      hstep H A hH.2.2.2.1 (p H hH) hH.2.2.1 hHB (hfixed H hH) (hradius H hH) (horder H hH)
        (haccuracy H hH) (hrecenter H hH) (Classical.choice (hrecords H hH))
        (hbfr H hH) (hctrl H hH) (hdebit H hH) s G hs hinit hsing
    refine ⟨Q, E, hE, hincoming, ?_⟩
    let K := H.appendEvent E.incoming.lt E hE
    have hp : H.toHistory.IsPrefixOf K.toHistory :=
      H.appendEvent_isPrefixOf E.incoming.lt E hE (hH.2.2.1 ▸ E.incoming.lt)
        (H.appendEventCompatible_of_time_eq_horizon E hH.2.2.1)
    refine ⟨hH.1.trans hp, hs, H.appendEvent_time_last E.incoming.lt E hE, hInvNext,
      (p H hH).spliceAt q s, hfixed H hH, hradius H hH, horder H hH,
      haccuracy H hH, hrecenter H hH, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hR := R.spliceParametersAt hqfixed hqradius hqorder hqaccuracy hqrecenter
        have ht : (H.appendEvent E.incoming.lt E hE).toHistory.time
            (Fin.last H.eventCount).succ = s :=
          H.appendEvent_time_last E.incoming.lt E hE
        exact Eq.mp (congrArg
          (fun q' => GeometricCutoffRecord (H.appendEvent E.incoming.lt E hE).toHistory
            (Fin.last H.eventCount) q') (congrArg ((p H hH).spliceAt q) ht)) hR
      · apply (GeometricCutoffRecord.appendEvent E.incoming.lt E hE
          (Classical.choice (hrecords H hH) j)).spliceParametersOfNe
        have ht : (H.appendEvent E.incoming.lt E hE).toHistory.time j.castSucc.succ =
            H.time j.succ := H.appendEvent_time_castSucc E.incoming.lt E hE j.succ
        intro heq
        exact (ne_of_lt ((H.time_strictMono.monotone (Fin.le_last j.succ)).trans_lt
          E.incoming.lt)) (ht.symm.trans heq)
    · intro i
      exact (H.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded
        E.incoming.lt E hE (hbfr H hH) (hctrl H hH) hbfrE hctrlE i).1
    · intro i
      exact (H.appendEvent_boundaryFrameReversing_and_poincareStandardDiscarded
        E.incoming.lt E hE (hbfr H hH) (hctrl H hH) hbfrE hctrlE i).2
    · exact H.appendEvent_compact_volume_debit E.incoming.lt E hE v
        (hdebit H hH) ⟨F, hF, hvol⟩
  exact H₀.exists_poincare_controlled_extinction_of_history_volume_debit
    (InitialIdentification.atZero P g) S hzero hv
    (fun H hH => hH.1) (fun H hH => hH.2.1) (fun H hH => hH.2.2.1)
    hdebit hclosed p (fun H hH => Classical.choice (hrecords H hH)) hbfr hctrl hc hscalar0 hthr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants

theorem exists_poincare_controlled_extinction_of_singular_events_of_invariant
    (P : OrientedThreeStage.{u}) [SimplyConnectedSpace P.Carrier] (g : P.Metric)
    (Inv : RetainedCoreHistory P → Prop) (hInv : Inv (RetainedCoreHistory.atZero P g))
    (hproduce : ∀ B : ℝ, 0 < B → ∃ (p₀ : CutoffParameters) (v : ℝ), 0 < v ∧
      ∀ H : RetainedCoreHistory P, InitialIdentification P g H.toHistory → Inv H →
        ∀ p : CutoffParameters,
        H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
        p.fixed = p₀.fixed → p.modelRadius = p₀.modelRadius →
        p.modelOrder = p₀.modelOrder → p.modelAccuracy = p₀.modelAccuracy →
        p.recenterConstant = p₀.recenterConstant →
        (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) →
        (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) →
          (∀ i : Fin H.eventCount,
            (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                (H.coreEvent i).outputMetric _root_.Set.univ +
                  ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
        ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s), s ≤ B →
          G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
          ∃ (Q : OrientedThreeStage.{u})
            (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
              (H.time (Fin.last H.eventCount)) s)
            (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
              (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
            (q : CutoffParameters),
            E.incoming = G ∧ Inv (H.appendEvent E.incoming.lt E hinit) ∧
            q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
            q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
            q.recenterConstant = p.recenterConstant ∧
            Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q) ∧ E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric _root_.Set.univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  apply exists_poincare_controlled_extinction_of_singular_events_of_horizon_invariants P g
  intro B hB
  obtain ⟨p₀, v, hv, hstep⟩ := hproduce B hB
  exact ⟨p₀, v, Inv, hv, hInv, hstep⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_invariant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_invariant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_invariant ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events_of_invariant

theorem exists_poincare_controlled_extinction_of_singular_events
    (P : OrientedThreeStage.{u}) [SimplyConnectedSpace P.Carrier] (g : P.Metric)
    (hproduce : ∀ B : ℝ, 0 < B → ∃ (p₀ : CutoffParameters) (v : ℝ), 0 < v ∧
      ∀ H : RetainedCoreHistory P, InitialIdentification P g H.toHistory →
        ∀ p : CutoffParameters,
        H.time (Fin.last H.eventCount) = H.horizon → H.horizon < B →
        p.fixed = p₀.fixed → p.modelRadius = p₀.modelRadius →
        p.modelOrder = p₀.modelOrder → p.modelAccuracy = p₀.modelAccuracy →
        p.recenterConstant = p₀.recenterConstant →
        (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) →
        (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) →
          (∀ i : Fin H.eventCount,
            (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) →
          (∀ i : Fin H.eventCount,
            ∃ F : Set (H.coreEvent i).incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier
                (H.coreEvent i).outputMetric _root_.Set.univ +
                  ENNReal.ofReal ((Nat.card (H.coreEvent i).transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel (H.coreEvent i).incoming.terminalRegularOpen
                (H.coreEvent i).terminal.metric F) →
        ∀ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s), s ≤ B →
          G.flow.base.metric (H.time (Fin.last H.eventCount)) =
            H.initialMetric (Fin.last H.eventCount) → G.SingularEndpoint →
          ∃ (Q : OrientedThreeStage.{u})
            (E : RetainedCoreEvent (H.stage (Fin.last H.eventCount)) Q
              (H.time (Fin.last H.eventCount)) s)
            (hinit : E.toMetricCutCapEvent.incoming.flow.base.metric
              (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))
            (q : CutoffParameters),
            E.incoming = G ∧
            q.fixed = p.fixed ∧ q.modelRadius = p.modelRadius ∧
            q.modelOrder = p.modelOrder ∧ q.modelAccuracy = p.modelAccuracy ∧
            q.recenterConstant = p.recenterConstant ∧
            Nonempty (GeometricCutoffRecord (H.appendEvent E.incoming.lt E hinit).toHistory
              (Fin.last H.eventCount) q) ∧ E.transition.boundaryFrameReversing ∧
            E.toMetricCutCapEvent.poincareStandardDiscarded ∧
            ∃ F : Set E.incoming.terminalRegularOpen, IsCompact F ∧
              riemannianVolumeMeasure ThreeModel Q.Carrier E.outputMetric _root_.Set.univ +
                ENNReal.ofReal ((Nat.card E.transition.trace.tubes.Index : ℝ) * v) ≤
              riemannianVolumeMeasure ThreeModel E.incoming.terminalRegularOpen
                E.terminal.metric F) :
    Nonempty (PoincareControlledExtinction P.toClosedOrientedManifold g) := by
  apply exists_poincare_controlled_extinction_of_singular_events_of_invariant P g
    (fun _ => True) trivial
  intro B hB
  obtain ⟨p₀, v, hv, hstep⟩ := hproduce B hB
  refine ⟨p₀, v, hv, ?_⟩
  intro H A _ p htime hHB hfixed hradius horder haccuracy hrecenter hrecords hbfr hctrl
    hdebit s G hs hinit hsing
  obtain ⟨Q, E, hE, q, hincoming, hqfixed, hqradius, hqorder, hqaccuracy, hqrecenter,
    hnew, hbfrE, hctrlE, F, hF, hvol⟩ :=
    hstep H A p htime hHB hfixed hradius horder haccuracy hrecenter hrecords hbfr hctrl
      hdebit s G hs hinit hsing
  exact ⟨Q, E, hE, q, hincoming, trivial, hqfixed, hqradius, hqorder, hqaccuracy,
    hqrecenter, hnew, hbfrE, hctrlE, F, hF, hvol⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_singular_events

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
