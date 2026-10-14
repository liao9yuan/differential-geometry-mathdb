import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingBackwardScalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

theorem TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen) {c : ℝ} (hac : a ≤ c) (hcs : c < s)
    (hbound : ∀ t ∈ _root_.Set.Ioo c s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) {t : ℝ} (ht : t ∈ _root_.Set.Ico c s) :
    |(_root_.Max.max q (G.flow.scalar t x.val))⁻¹ - (_root_.Max.max q (metricScalarAt L.metric x))⁻¹| ≤
      C * (s - t) := by
  have hlip : LipschitzOnWith C (fun t => (_root_.Max.max q (G.flow.scalar t x.val))⁻¹) (_root_.Set.Ioo c s) := by
    apply DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound
      (r' := fun t => derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t)
      hq _root_.Set.ordConnected_Ioo
    · intro t ht
      exact (G.equation.scalarTime (K := _root_.Set.Ioo c s) ht (fun _ ht => ⟨hac.trans ht.1.le, ht.2⟩) x.val).continuousWithinAt
    · intro t ht _
      exact hasDerivWithinAt_left_of_mem_nhdsLE
        (G.equation.scalarTime (K := _root_.Set.Ioo c s) ht (fun _ ht => ⟨hac.trans ht.1.le, ht.2⟩) x.val)
        (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds ht.1 ht.2))
    · exact hbound
  have hlimTerminal : _root_.Filter.Tendsto (fun t => (_root_.Max.max q (G.flow.scalar t x.val))⁻¹)
      (𝓝[<] s) (𝓝 ((_root_.Max.max q (metricScalarAt L.metric x))⁻¹)) := by
    exact ((tendsto_const_nhds.max (L.tendsto_metricScalarAt x)).inv₀
      (ne_of_gt (hq.trans_le (le_max_left _ _))))
  have hpoint (t : ℝ) (ht : t ∈ _root_.Set.Ioo c s) :
      |(_root_.Max.max q (G.flow.scalar t x.val))⁻¹ - (_root_.Max.max q (metricScalarAt L.metric x))⁻¹| ≤
        C * (s - t) := by
    apply le_of_tendsto_of_tendsto
      ((tendsto_const_nhds.sub hlimTerminal).abs)
      (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds |>.sub_const t))
    filter_upwards [Ioo_mem_nhdsLT ht.2] with u hu
    have h := hlip.dist_le_mul t ht u ⟨ht.1.trans hu.1,hu.2⟩
    simpa only [id_eq, Real.dist_eq, abs_sub_comm t u,
      abs_of_nonneg (sub_nonneg.mpr hu.1.le)] using h
  rcases eq_or_lt_of_le ht.1 with hta | hta
  · have he : t = c := hta.symm
    subst t
    have hlimInitial : _root_.Filter.Tendsto (fun t => (_root_.Max.max q (G.flow.scalar t x.val))⁻¹)
        (𝓝[>] c) (𝓝 ((_root_.Max.max q (G.flow.scalar c x.val))⁻¹)) := by
      have hc := G.equation.scalarTime (K := _root_.Set.Ico c s) ⟨le_rfl,hcs⟩ (fun _ ht => ⟨hac.trans ht.1,ht.2⟩) x.val
      have hcont := hc.continuousWithinAt
      have hm : _root_.Filter.Tendsto (fun t => G.flow.scalar t x.val) (𝓝[>] c)
          (𝓝 (G.flow.scalar c x.val)) := by
        have hIco : _root_.Set.Ico c s ∈ 𝓝[>] c :=
          _root_.Filter.mem_of_superset (Ioo_mem_nhdsGT hcs) (fun _ ht => ⟨ht.1.le, ht.2⟩)
        exact hcont.mono_left (nhdsWithin_le_of_mem hIco)
      exact ((tendsto_const_nhds.max hm).inv₀
        (ne_of_gt (hq.trans_le (le_max_left _ _))))
    apply le_of_tendsto_of_tendsto ((hlimInitial.sub tendsto_const_nhds).abs)
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub
        (tendsto_id.mono_left nhdsWithin_le_nhds)))
    filter_upwards [Ioo_mem_nhdsGT hcs] with t ht
    exact hpoint t ht
  · exact hpoint t ⟨hta, ht.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le_on_time_window

theorem TerminalLimitMetric.inv_max_scalar_sub_terminal_le
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) {t : ℝ} (ht : t ∈ _root_.Set.Ico a s) :
    |(_root_.Max.max q (G.flow.scalar t x.val))⁻¹ - (_root_.Max.max q (metricScalarAt L.metric x))⁻¹| ≤
      C * (s - t) := by
  exact L.inv_max_scalar_sub_terminal_le_on_time_window G hq x le_rfl G.lt hbound ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_sub_terminal_le

theorem TerminalLimitMetric.inv_max_scalar_initial_sub_terminal_le
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (x : G.terminalRegularOpen)
    (hbound : ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x.val →
      |derivWithin (fun v => G.flow.scalar v x.val) (_root_.Set.Iic t) t| ≤
        C * G.flow.scalar t x.val ^ 2) :
    |(_root_.Max.max q (G.flow.scalar a x.val))⁻¹ - (_root_.Max.max q (metricScalarAt L.metric x))⁻¹| ≤
      C * (s - a) :=
  L.inv_max_scalar_sub_terminal_le G hq x hbound ⟨le_rfl, G.lt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_initial_sub_terminal_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_initial_sub_terminal_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_initial_sub_terminal_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.inv_max_scalar_initial_sub_terminal_le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
