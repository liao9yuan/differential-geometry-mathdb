import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventAction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instMeasurableSpaceCarrier : MeasurableSpace P.Carrier := borel P.Carrier

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instMeasurableSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instMeasurableSpaceCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instBorelSpaceCarrier : BorelSpace P.Carrier := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instBorelSpaceCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instBorelSpaceCarrier target :: scope.openDecls } }

def eventRegularizedC1Density (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier) : ℝ≥0∞ :=
  ⨆ A ∈ E.eventRegularizedC1ActionValues G T d v p q,
    ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density

theorem eventRegularizedC1Density_eq_zero_of_no_competitor
    (T d v : ℝ) (p : Q.Carrier) (q : P.Carrier)
    (h : E.eventRegularizedC1ActionValues G T d v p q = ∅) :
    E.eventRegularizedC1Density G T d v p q = 0 := by
  simp [eventRegularizedC1Density, h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_zero_of_no_competitor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_zero_of_no_competitor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_zero_of_no_competitor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_zero_of_no_competitor

theorem le_eventRegularizedC1Density_of_action_le
    (T d : ℝ) {v L A : ℝ} (hv : 0 < v) (p : Q.Carrier) (q : P.Carrier)
    (hA : A ∈ E.eventRegularizedC1ActionValues G T d v p q) (hAL : A ≤ L) :
    ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤ E.eventRegularizedC1Density G T d v p q := by
  apply le_trans _ (le_iSup_of_le A (le_iSup_of_le hA le_rfl))
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right (neg_le_neg hAL) (by positivity : 0 ≤ 2 * v)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.le_eventRegularizedC1Density_of_action_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.le_eventRegularizedC1Density_of_action_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.le_eventRegularizedC1Density_of_action_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.le_eventRegularizedC1Density_of_action_le

theorem eventRegularizedC1Density_eq_of_minimum
    (T d : ℝ) {v A : ℝ} (hv : 0 < v) (p : Q.Carrier) (q : P.Carrier)
    (hA : A ∈ E.eventRegularizedC1ActionValues G T d v p q)
    (hmin : ∀ L ∈ E.eventRegularizedC1ActionValues G T d v p q, A ≤ L) :
    E.eventRegularizedC1Density G T d v p q =
      ENNReal.ofReal (Real.exp (-A / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) := by
  apply le_antisymm
  · apply iSup_le
    intro L
    apply iSup_le
    intro hL
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_right (neg_le_neg (hmin L hL)) (by positivity : 0 ≤ 2 * v)
    linarith
  · exact E.le_eventRegularizedC1Density_of_action_le G T d hv p q hA le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_of_minimum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_of_minimum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_of_minimum ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.eventRegularizedC1Density_eq_of_minimum

theorem volume_mul_exp_le_lintegral_eventRegularizedC1Density
    (T d : ℝ) {v L : ℝ} (hv : 0 < v) (p : Q.Carrier) {U : Set P.Carrier}
    (hU : MeasurableSet U)
    (haccess : ∀ q ∈ U, ∃ A ∈ E.eventRegularizedC1ActionValues G T d v p q, A ≤ L) :
    riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U *
      ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
      ∫⁻ q in U, E.eventRegularizedC1Density G T d v p q
        ∂riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) := by
  let μ := riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2))
  let c := ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
    (3 / 2 : ℝ) * Real.log (4 * Real.pi)))
  have hh : (∫⁻ _q in U, c ∂μ) ≤ ∫⁻ q in U, E.eventRegularizedC1Density G T d v p q ∂μ := by
    apply _root_.MeasureTheory.lintegral_mono_ae
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hU] with q hq
    obtain ⟨A, hA, hAL⟩ := haccess q hq
    exact E.le_eventRegularizedC1Density_of_action_le G T d hv p q hA hAL
  simpa only [_root_.MeasureTheory.lintegral_const, Measure.restrict_apply_univ, mul_comm, μ, c] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.volume_mul_exp_le_lintegral_eventRegularizedC1Density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.volume_mul_exp_le_lintegral_eventRegularizedC1Density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.volume_mul_exp_le_lintegral_eventRegularizedC1Density ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.volume_mul_exp_le_lintegral_eventRegularizedC1Density

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)
  (G : Q.IncomingSlab s b)
  {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
  (f : X → P.Carrier) (g : X → Q.Carrier)
  (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
  (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
  (hcross : ∀ z : X, E.RegularCrossing (f z) (g z))

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instMeasurableSpaceCarrier_1 : MeasurableSpace P.Carrier := borel P.Carrier

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instMeasurableSpaceCarrier_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instMeasurableSpaceCarrier_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instBorelSpaceCarrier_1 : BorelSpace P.Carrier := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instBorelSpaceCarrier_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instBorelSpaceCarrier_1 target :: scope.openDecls } }

include hcross in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_open_pos_eventRegularizedC1Density_mass_of_survivor_seed
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (hS : IsSolutionOn S) (T : ℝ) {d v L : ℝ} (hd : 0 < d) (hdv : d < v)
    (hclock : T - d ^ 2 = s)
    (hcarrier : ∀ r ∈ _root_.Set.Icc 0 v, T - r ^ 2 ∈ D.carrier)
    (htimePlus : ∀ r ∈ _root_.Set.Icc 0 d, T - r ^ 2 ∈ (RealTimeInterval.closedOpen s b G.lt).carrier)
    (htimeMinus : ∀ r ∈ _root_.Set.Ioc d v, T - r ^ 2 ∈ (RealTimeInterval.closedOpen a s E.incoming.lt).carrier)
    (hbefore : ∀ r ∈ _root_.Set.Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ _root_.Set.Ioo 0 d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (η : ℝ → X) (hη : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η)
    (hseed : lRegularizedAction S T η 0 v < L) :
    ∃ U : Set P.Carrier, IsOpen U ∧ f (η v) ∈ U ∧ U ⊆ _root_.Set.range f ∧
      0 < riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U ∧
      riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) U *
        ENNReal.ofReal (Real.exp (-L / (2 * v) - (3 / 2 : ℝ) * Real.log (v ^ 2) -
          (3 / 2 : ℝ) * Real.log (4 * Real.pi))) ≤
        ∫⁻ q in U, E.eventRegularizedC1Density G T d v (g (η 0)) q
          ∂riemannianVolumeMeasure ThreeModel P.Carrier (E.incoming.flow.base.metric (T - v ^ 2)) := by
  obtain ⟨V, hV, hηV, α, hα, hstart, hend, _, hact⟩ :=
    exists_open_endpoint_family_of_lRegularizedAction_lt S hS T (hd.trans hdv) hcarrier η hη hseed
  have hopen : IsOpen (f '' V) := hf.isOpenMap V hV
  refine ⟨f '' V, hopen, ⟨η v, hηV, rfl⟩, _root_.Set.image_subset_range _ _, ?_, ?_⟩
  · let _ : (riemannianVolumeMeasure ThreeModel P.Carrier
        (E.incoming.flow.base.metric (T - v ^ 2))).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure _
    exact hopen.measure_pos _ ⟨_, ⟨η v, hηV, rfl⟩⟩
  · apply E.volume_mul_exp_le_lintegral_eventRegularizedC1Density G T d (hd.trans hdv)
      (g (η 0)) hopen.measurableSet
    rintro y ⟨z, hz, rfl⟩
    refine ⟨lRegularizedAction S T (α z) 0 v, ?_, (hact z hz).le⟩
    have hmem := E.action_mem_eventRegularizedC1ActionValues_of_survivor_curve G f g hf hg hcross
      S hS T hd hdv hclock hcarrier htimePlus htimeMinus
      hbefore hafter (α z) (hα z hz)
    simpa only [hstart z hz, hend z hz] using hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_open_pos_eventRegularizedC1Density_mass_of_survivor_seed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_open_pos_eventRegularizedC1Density_mass_of_survivor_seed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_open_pos_eventRegularizedC1Density_mass_of_survivor_seed ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_open_pos_eventRegularizedC1Density_mass_of_survivor_seed

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
