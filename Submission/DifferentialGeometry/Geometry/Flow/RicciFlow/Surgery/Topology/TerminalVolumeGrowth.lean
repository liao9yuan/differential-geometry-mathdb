import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EndpointAntitone
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instMeasurableSpaceCarrier : MeasurableSpace P.Carrier := borel P.Carrier

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instMeasurableSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instMeasurableSpaceCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instBorelSpaceCarrier : BorelSpace P.Carrier := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instBorelSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instBorelSpaceCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instMeasurableSpaceSubtypeCarrierMemOpensTerminalRegularOpen : MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instMeasurableSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instMeasurableSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instBorelSpaceSubtypeCarrierMemOpensTerminalRegularOpen : BorelSpace G.terminalRegularOpen := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instBorelSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instBorelSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpen target :: scope.openDecls } }

theorem volume_le_exp_mul_initial {K : ℝ}
    (hscalar : ∀ t ∈ _root_.Set.Ico a s, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x) {t : ℝ} (ht : t ∈ _root_.Set.Ico a s) :
    riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t) _root_.Set.univ ≤
      ENNReal.ofReal (Real.exp (K * (t - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ := by
  obtain ⟨b, htb, hbs⟩ := exists_between ht.2
  let S := G.closedPrefix b (ht.1.trans_lt htb) hbs
  have hbound := S.exp_mul_volume_le_endpoint K
    (fun u hu x => hscalar u ⟨hu.1, hu.2.trans_lt hbs⟩ x)
    t ⟨ht.1, htb.le⟩
  change Real.exp (-K * t) *
      (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t) _root_.Set.univ).toReal ≤
    Real.exp (-K * a) *
      (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) _root_.Set.univ).toReal at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (K * t)).le
  have hcancel : Real.exp (K * t) * Real.exp (-K * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hweight : Real.exp (K * t) * Real.exp (-K * a) = Real.exp (K * (t - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hcancel, one_mul, ← mul_assoc, hweight] at hmul
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (G.flow.base.metric a)
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (G.flow.base.metric t)
  apply (ENNReal.toReal_le_toReal (_root_.MeasureTheory.measure_ne_top _ _) ?_).mp
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hmul
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (_root_.MeasureTheory.measure_ne_top _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.volume_le_exp_mul_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.volume_le_exp_mul_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.volume_le_exp_mul_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.volume_le_exp_mul_initial

theorem TerminalLimitMetric.volume_compact_le_exp_mul_initial
    (L : G.TerminalLimitMetric) {K : ℝ}
    (hscalar : ∀ t ∈ _root_.Set.Ico a s, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x)
    {F : Set G.terminalRegularOpen} (hF : IsCompact F) :
    riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric F ≤
      ENNReal.ofReal (Real.exp (K * (s - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ := by
  have hconv : _root_.Filter.Tendsto (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (K * (t - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) _root_.Set.univ)
      (𝓝[<] s) (𝓝 (ENNReal.ofReal (Real.exp (K * (s - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) _root_.Set.univ)) := by
    let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (G.flow.base.metric a)
    apply ENNReal.Tendsto.mul_const _ (Or.inr (_root_.MeasureTheory.measure_ne_top _ _))
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    exact ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
  apply le_of_tendsto_of_tendsto (L.tendsto_riemannianVolumeMeasure_compact hF) hconv
  filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
  have hmap := congrArg (fun μ : _root_.MeasureTheory.Measure P.Carrier => μ _root_.Set.univ)
    (map_riemannianVolumeMeasure_restrictOpen (G.flow.base.metric t) G.terminalRegularOpen)
  rw [Measure.map_apply continuous_subtype_val.measurable MeasurableSet.univ,
    _root_.Set.preimage_univ, Measure.restrict_apply_univ] at hmap
  exact ((_root_.MeasureTheory.measure_mono (_root_.Set.subset_univ F)).trans hmap.le).trans
    ((_root_.MeasureTheory.measure_mono (_root_.Set.subset_univ _)).trans (G.volume_le_exp_mul_initial hscalar ⟨ht.1.le, ht.2⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.volume_compact_le_exp_mul_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.volume_compact_le_exp_mul_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.volume_compact_le_exp_mul_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.volume_compact_le_exp_mul_initial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
