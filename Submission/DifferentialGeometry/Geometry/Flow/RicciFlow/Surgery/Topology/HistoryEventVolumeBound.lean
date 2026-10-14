import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryComponentCount
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryVolumeDebit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.BigOperators _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceCarrier (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier := borel P.Carrier

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceCarrier (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instMeasurableSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    BorelSpace G.terminalRegularOpen := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instBorelSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

theorem ObservedHistory.eventCount_le_card_initial_add_volume_bound
    (H : ObservedHistory.{u}) {v K T : ℝ} (hv : 0 < v)
    (hK : 0 ≤ K) (hT : H.horizon ≤ T)
    (hscalar : ∀ i : Fin H.eventCount, ∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier,
      -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric _root_.Set.univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * (Real.exp (K * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) _root_.Set.univ).toReal / v) := by
  have hc : (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) := by
    exact_mod_cast H.eventCount_le_card_initial_add_two_mul_sum_card_cut
  have hvb := H.sum_cut_count_mul_le_exp_mul_initial_volume hv.le hK hT hscalar hcap
  have hb := (le_div_iff₀ hv).mpr hvb
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound

theorem ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    {v T : ℝ} (hv : 0 < v) (hT : H.horizon ≤ T)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric _root_.Set.univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * v) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * (Real.exp ((3 / a₀) * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) _root_.Set.univ).toReal / v) := by
  have hc : (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) := by
    exact_mod_cast H.eventCount_le_card_initial_add_two_mul_sum_card_cut
  have hvb := H.sum_cut_count_mul_le_of_fixedHamiltonIveyRegion
    records ha₀ hfixed hlower hv.le hT hcap
  have hb := (le_div_iff₀ hv).mpr hvb
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion

theorem exists_pos_volume_debit_and_eventCount_bound_of_finite_scales
    {β : Type*} [Finite β] (scale : β → ℝ) (hscale : ∀ b, 0 < scale b) :
    ∃ v : ℝ, 0 < v ∧ (∀ b, v ≤ scale b ^ (-3 / 2 : ℝ)) ∧
      ∀ (H : ObservedHistory.{u}) (bin : Fin H.eventCount → β) {K T : ℝ},
      0 ≤ K → H.horizon ≤ T →
      (∀ i : Fin H.eventCount, ∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ),
        ∀ x : (H.stage i.castSucc).Carrier,
        -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x) →
      (∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
        IsCompact F ∧
        riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric _root_.Set.univ +
          ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) *
            scale (bin i) ^ (-3 / 2 : ℝ)) ≤
        riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
          (H.event i).terminal.metric F) →
      (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
        2 * (Real.exp (K * T) *
          (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
            (H.initialMetric 0) _root_.Set.univ).toReal / v) := by
  obtain ⟨v, hv, hle, hbound⟩ := exists_pos_volume_debit_of_finite_scales scale hscale
  refine ⟨v, hv, hle, ?_⟩
  intro H bin K T hK hT hscalar hcap
  have hc : (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * ∑ i : Fin H.eventCount, (Nat.card (H.event i).transition.trace.tubes.Index : ℝ) := by
    exact_mod_cast H.eventCount_le_card_initial_add_two_mul_sum_card_cut
  have hb := hbound H bin hK hT hscalar hcap
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_volume_debit_and_eventCount_bound_of_finite_scales then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_volume_debit_and_eventCount_bound_of_finite_scales"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_volume_debit_and_eventCount_bound_of_finite_scales ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_volume_debit_and_eventCount_bound_of_finite_scales

theorem ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le
    (H : ObservedHistory.{u}) (scale : Fin H.eventCount → ℝ)
    {Q K T : ℝ} (hQ : 0 < Q) (hscale : ∀ i, 0 < scale i)
    (hscale_le : ∀ i, scale i ≤ Q)
    (hK : 0 ≤ K) (hT : H.horizon ≤ T)
    (hscalar : ∀ i : Fin H.eventCount, ∀ t ∈ _root_.Set.Ico (H.time i.castSucc) (H.time i.succ),
      ∀ x : (H.stage i.castSucc).Carrier,
      -K ≤ metricScalarAt ((H.event i).incoming.flow.base.metric t) x)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric _root_.Set.univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * scale i ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * (Real.exp (K * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) _root_.Set.univ).toReal / Q ^ (-3 / 2 : ℝ)) := by
  apply H.eventCount_le_card_initial_add_volume_bound (Real.rpow_pos_of_pos hQ _) hK hT hscalar
  intro i
  obtain ⟨F, hF, hvol⟩ := hcap i
  refine ⟨F, hF, le_trans ?_ hvol⟩
  apply add_le_add_right
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos (hscale i) (hscale_le i) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le

theorem ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le_of_fixedHamiltonIveyRegion
    (H : ObservedHistory.{u}) {parameters : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hfixed : ∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x)
    (hlower : ∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x)
    (scale : Fin H.eventCount → ℝ) {Q T : ℝ} (hQ : 0 < Q)
    (hscale : ∀ i, 0 < scale i) (hscale_le : ∀ i, scale i ≤ Q) (hT : H.horizon ≤ T)
    (hcap : ∀ i : Fin H.eventCount, ∃ F : Set (H.event i).incoming.terminalRegularOpen,
      IsCompact F ∧
      riemannianVolumeMeasure ThreeModel (H.stage i.succ).Carrier (H.event i).outputMetric _root_.Set.univ +
        ENNReal.ofReal ((Nat.card (H.event i).transition.trace.tubes.Index : ℝ) * scale i ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure ThreeModel (H.event i).incoming.terminalRegularOpen
        (H.event i).terminal.metric F) :
    (H.eventCount : ℝ) ≤ Nat.card (ConnectedComponents (H.stage 0).Carrier) +
      2 * (Real.exp ((3 / a₀) * T) *
        (riemannianVolumeMeasure ThreeModel (H.stage 0).Carrier
          (H.initialMetric 0) _root_.Set.univ).toReal / Q ^ (-3 / 2 : ℝ)) := by
  apply H.eventCount_le_card_initial_add_volume_bound_of_fixedHamiltonIveyRegion
    records ha₀ hfixed hlower (Real.rpow_pos_of_pos hQ _) hT
  intro i
  obtain ⟨F, hF, hvol⟩ := hcap i
  refine ⟨F, hF, le_trans ?_ hvol⟩
  apply add_le_add_right
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Real.rpow_le_rpow_of_nonpos (hscale i) (hscale_le i) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le_of_fixedHamiltonIveyRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le_of_fixedHamiltonIveyRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le_of_fixedHamiltonIveyRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventCount_le_card_initial_add_volume_bound_of_scale_le_of_fixedHamiltonIveyRegion

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
