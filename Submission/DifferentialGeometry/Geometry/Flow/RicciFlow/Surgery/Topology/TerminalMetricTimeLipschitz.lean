import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricJetBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.TimeLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier : IsManifold ThreeModel 1 P.Carrier := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier_1 : IsManifold ThreeModel 2 P.Carrier := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.instIsManifoldRealThreeSpaceThreeModelOfNatWithTopENatCarrier_1 target :: scope.openDecls } }

theorem IncomingSlab.exists_terminalRegular_metric_time_lipschitz
    (G : P.IncomingSlab a s) {x : P.Carrier} (hx : x ∈ G.terminalRegularRegion) (N : ℕ) :
    ∃ (V : Set P.Carrier) (c L : ℝ), IsOpen V ∧ x ∈ V ∧ c ∈ _root_.Set.Ioo a s ∧ 0 ≤ L ∧
      ∀ q ≤ N, ∀ t ∈ _root_.Set.Ico c s, ∀ u ∈ _root_.Set.Ico c s, ∀ y ∈ V,
        metricDerivNorm q (G.flow.base.metric t) (G.flow.base.metric u)
          (G.flow.base.metric a) y ≤ L * |t - u| := by
  classical
  obtain ⟨V, c, B, A, C, hV, hxV, _, _, hc, hB, _, hC, heq, hcurv, hjets⟩ :=
    G.exists_terminalRegular_fixed_reference_metric_jets hx
  let gRef := G.flow.base.metric a
  let gSeq : ℕ → ℝ → P.Metric := fun _ t => G.flow.base.metric t
  obtain ⟨KShi, hKShi, hShiOf⟩ :=
    exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
      (I := ThreeModel) (M := P.Carrier) N A
  have heqV : ∀ t ∈ _root_.Set.Ico c s, MetricUniformEquivalentOn V gRef (G.flow.base.metric t) B :=
    fun t ht => ⟨hB, fun y hy v => (heq t ht).2 y (subset_closure hy) v⟩
  have hjetsV : ∀ r, 1 ≤ r → r ≤ N → ∀ t ∈ _root_.Set.Ico c s, ∀ y ∈ V,
      metricCovDerivNorm r (G.flow.base.metric t) gRef y ≤ C r := by
    intro r _ _ t ht y hy
    exact hjets r r le_rfl t ht y (subset_closure hy)
  have hshiW : ∀ ψ ∈ _root_.Set.Ico c s, MovingShiBoundOn V c ψ gSeq N KShi := by
    intro ψ hψ
    exact hShiOf gSeq V c ψ (fun m _ i t ht y hy =>
      hcurv m t ⟨ht.1, ht.2.trans_lt hψ.2⟩ y (subset_closure hy))
  have hqLip : ∀ q : ℕ, q ≤ N → ∃ L : ℝ, 0 ≤ L ∧
      ∀ t ∈ _root_.Set.Ico c s, ∀ u ∈ _root_.Set.Ico c s, ∀ y ∈ V,
        metricDerivNorm q (G.flow.base.metric t) (G.flow.base.metric u) gRef y ≤ L * |t - u| := by
    intro q hq
    obtain ⟨L, hL, hbound⟩ := exists_metric_time_lipschitz_constant_of_local_evolution
      hV gRef hB N C hKShi q hq
    refine ⟨L, hL, hbound G.flow.base.metric heqV hjetsV hshiW ?_⟩
    intro t ht y hy slots
    have he := hevComp_of_solutions (I := ThreeModel) (β := c) (ψ := t) (N := q)
      (gSeq := gSeq) (gRef := gRef)
      (fun _ => RealTimeInterval.closedOpen a s G.lt) (fun _ => G.flow)
      (fun _ => G.equation) (fun _ _ => rfl)
      (fun _ r hr => ⟨hc.1.trans_le hr.1, hr.2.trans_lt ht.2⟩)
      (fun _ p hp V x₀ => solutionTowerSwap_regularity gRef G.flow G.equation q
        (fun {_} hr => (RealTimeInterval.closedOpen a s G.lt).regular_isOpen.mem_nhds hr)
        p hp V x₀)
    exact he 0 y t ⟨ht.1, le_rfl⟩ slots
  have hall : ∀ q : ℕ, ∃ L : ℝ, 0 ≤ L ∧ (q ≤ N →
      ∀ t ∈ _root_.Set.Ico c s, ∀ u ∈ _root_.Set.Ico c s, ∀ y ∈ V,
        metricDerivNorm q (G.flow.base.metric t) (G.flow.base.metric u) gRef y ≤ L * |t - u|) := by
    intro q
    by_cases hq : q ≤ N
    · obtain ⟨L, hL, hlip⟩ := hqLip q hq
      exact ⟨L, hL, fun _ => hlip⟩
    · exact ⟨0, le_rfl, fun h => (hq h).elim⟩
  choose L hL hLb using hall
  refine ⟨V, c, ∑ q ∈ Finset.range (N + 1), L q, hV, hxV, hc,
    Finset.sum_nonneg (fun q _ => hL q), ?_⟩
  intro q hq t ht u hu y hy
  exact (hLb q hq t ht u hu y hy).trans
    (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun r _ => hL r) (Finset.mem_range.mpr (by omega))) (abs_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_metric_time_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_metric_time_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_metric_time_lipschitz ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_metric_time_lipschitz

theorem IncomingSlab.exists_metric_time_lipschitz_on_compact_regularRegion
    (G : P.IncomingSlab a s) {K : Set P.Carrier} (hK : IsCompact K)
    (hKreg : K ⊆ G.terminalRegularRegion) (N : ℕ) :
    ∃ c ∈ _root_.Set.Ioo a s, ∃ L : ℝ, 0 ≤ L ∧
      ∀ q ≤ N, ∀ t ∈ _root_.Set.Ico c s, ∀ u ∈ _root_.Set.Ico c s, ∀ y ∈ K,
        metricDerivNorm q (G.flow.base.metric t) (G.flow.base.metric u)
          (G.flow.base.metric a) y ≤ L * |t - u| := by
  classical
  have hlocal : ∀ x : K, ∃ (V : Set P.Carrier) (c L : ℝ),
      IsOpen V ∧ (x : P.Carrier) ∈ V ∧ c ∈ _root_.Set.Ioo a s ∧ 0 ≤ L ∧
      ∀ q ≤ N, ∀ t ∈ _root_.Set.Ico c s, ∀ u ∈ _root_.Set.Ico c s, ∀ y ∈ V,
        metricDerivNorm q (G.flow.base.metric t) (G.flow.base.metric u)
          (G.flow.base.metric a) y ≤ L * |t - u| :=
    fun x => G.exists_terminalRegular_metric_time_lipschitz (hKreg x.2) N
  choose V c L hV hxV hc hL hLb using hlocal
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover V hV
    (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩)
  have hbase : ∀ᶠ t in 𝓝[<] s, t ∈ _root_.Set.Ioo a s := Ioo_mem_nhdsLT G.lt
  have htimes : ∀ᶠ t in 𝓝[<] s, t ∈ _root_.Set.Ioo a s ∧ ∀ x ∈ F, t ∈ _root_.Set.Ico (c x) s :=
    hbase.and
      ((Filter.eventually_all_finset F).mpr (fun x _ => Ico_mem_nhdsLT (hc x).2))
  obtain ⟨d, hd, hdF⟩ := htimes.exists
  refine ⟨d, hd, ∑ x ∈ F, L x, Finset.sum_nonneg (fun x _ => hL x), ?_⟩
  intro q hq t ht u hu y hy
  obtain ⟨x, hxF, hyV⟩ := mem_iUnion₂.mp (hF hy)
  exact (hLb x q hq t ⟨(hdF x hxF).1.trans ht.1, ht.2⟩
    u ⟨(hdF x hxF).1.trans hu.1, hu.2⟩ y hyV).trans
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun x _ => hL x) hxF) (abs_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_metric_time_lipschitz_on_compact_regularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_metric_time_lipschitz_on_compact_regularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_metric_time_lipschitz_on_compact_regularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_metric_time_lipschitz_on_compact_regularRegion

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
