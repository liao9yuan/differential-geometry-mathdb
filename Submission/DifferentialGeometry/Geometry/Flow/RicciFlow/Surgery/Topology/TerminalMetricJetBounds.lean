import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricEquivalence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalRegularCurvatureDerivatives
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.CovariantDerivative.Tail
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.MovingShi
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

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

theorem IncomingSlab.metric_jet_bounds_of_curvature_derivative_tail
    (G : P.IncomingSlab a s) {c : ℝ} (hac : a < c)
    {K U : Set P.Carrier} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (gRef : P.Metric) {B : ℝ} (hB : 1 ≤ B)
    (hequiv : ∀ t ∈ _root_.Set.Ico c s, MetricUniformEquivalentOn U gRef (G.flow.base.metric t) B)
    (N : ℕ) (A : ℕ → ℝ)
    (hcurv : ∀ m ≤ N, ∀ t ∈ _root_.Set.Ico c s, ∀ x ∈ U,
      curvDerivNorm m (G.flow.base.metric t) x ≤ A m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ≤ N, ∀ t ∈ _root_.Set.Ico c s, ∀ x ∈ K,
      metricCovDerivNorm r (G.flow.base.metric t) gRef x ≤ C := by
  classical
  let gSeq : ℕ → ℝ → P.Metric := fun _ t => G.flow.base.metric t
  obtain ⟨KShi, hKShi, hShiOf⟩ :=
    exists_movingShiBoundOn_constant_of_curvature_derivative_bounds
      (I := ThreeModel) (M := P.Carrier) N A
  obtain ⟨initialC, hinitC, hinit⟩ := exists_initialC (G.flow.base.metric c) gRef
  have heqW : ∀ ψ ∈ _root_.Set.Ico c s,
      MetricUniformEquivalentOnWindow U c ψ gRef gSeq (fun _ => B) := by
    intro ψ hψ i t ht
    exact hequiv t ⟨ht.1, ht.2.trans_lt hψ.2⟩
  have hshiW : ∀ ψ ∈ _root_.Set.Ico c s, MovingShiBoundOn U c ψ gSeq N KShi := by
    intro ψ hψ
    exact hShiOf gSeq U c ψ (fun m hm i t ht x hx =>
      hcurv m hm t ⟨ht.1, ht.2.trans_lt hψ.2⟩ x hx)
  have hev : ∀ ψ ∈ _root_.Set.Ico c s, ∀ q : ℕ, 1 ≤ q → q ≤ N →
      ∀ i : ℕ, ∀ x ∈ U, ∀ t ∈ _root_.Set.Icc c ψ,
        ∀ v : Fin (q + 2) → TangentSpace ThreeModel x,
          HasDerivAt (fun r : ℝ => metricCovDeriv (gSeq i r) gRef q x v)
            (((-2 : ℝ) • nablaRicReal gSeq gRef q i t x) v) t := by
    intro ψ hψ q _ _ i x _
    exact (hevComp_of_solutions (I := ThreeModel) (β := c) (ψ := ψ) (N := q)
      (fun _ => RealTimeInterval.closedOpen a s G.lt) (fun _ => G.flow)
      (fun _ => G.equation) (fun _ _ => rfl)
      (fun _ t ht => ⟨hac.trans_le ht.1, ht.2.trans_lt hψ.2⟩)
      (fun _ p hp V x₀ => solutionTowerSwap_regularity gRef G.flow G.equation q
        (fun {_} ht => (RealTimeInterval.closedOpen a s G.lt).regular_isOpen.mem_nhds ht)
        p hp V x₀)) i x
  have hp := covOrder_Ico_tail hK hU hKU N B hB KShi hKShi initialC hinitC (s - c)
    (fun _ => B) heqW (fun _ _ => le_rfl) hshiW hev
    (fun q _ _ _ x _ => hinit q x) (fun t ht => by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact sub_le_sub_right ht.2.le c)
  have hlevels : ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      (r ≤ N → ∀ t ∈ _root_.Set.Ico c s, ∀ x ∈ K,
        metricCovDerivNorm r (G.flow.base.metric t) gRef x ≤ C) := by
    intro r
    by_cases hr : r ≤ N
    · by_cases hr0 : r = 0
      · subst r
        refine ⟨B * Real.sqrt (Module.finrank ℝ ThreeSpace), by positivity, ?_⟩
        intro _ t ht x hx
        exact covOrder_zero_le (G.flow.base.metric t) gRef (hequiv t ht) x (hKU hx)
      · obtain ⟨C, hC⟩ := hp r (Nat.one_le_iff_ne_zero.mpr hr0) hr
        exact ⟨max C 0, le_max_right _ _, fun _ t ht x hx =>
          (hC 0 t ht x hx).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => (hr h).elim⟩
  choose C hC hbounds using hlevels
  refine ⟨∑ r ∈ Finset.range (N + 1), C r, Finset.sum_nonneg (fun r _ => hC r), ?_⟩
  intro r hr t ht x hx
  exact (hbounds r hr t ht x hx).trans
    (Finset.single_le_sum (fun q _ => hC q) (Finset.mem_range.mpr (by omega)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_jet_bounds_of_curvature_derivative_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_jet_bounds_of_curvature_derivative_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_jet_bounds_of_curvature_derivative_tail ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.metric_jet_bounds_of_curvature_derivative_tail

theorem IncomingSlab.exists_terminalRegular_fixed_reference_metric_jets
    (G : P.IncomingSlab a s) {x : P.Carrier} (hx : x ∈ G.terminalRegularRegion) :
    ∃ (V : Set P.Carrier) (c B : ℝ) (A C : ℕ → ℝ),
      IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ G.terminalRegularRegion ∧
      c ∈ _root_.Set.Ioo a s ∧ 1 ≤ B ∧ (∀ q, 0 ≤ A q) ∧ (∀ q, 0 ≤ C q) ∧
      (∀ t ∈ _root_.Set.Ico c s,
        MetricUniformEquivalentOn (closure V) (G.flow.base.metric a) (G.flow.base.metric t) B) ∧
      (∀ q t, t ∈ _root_.Set.Ico c s → ∀ y ∈ closure V,
        curvDerivNorm q (G.flow.base.metric t) y ≤ A q) ∧
      (∀ N r, r ≤ N → ∀ t ∈ _root_.Set.Ico c s, ∀ y ∈ closure V,
        metricCovDerivNorm r (G.flow.base.metric t) (G.flow.base.metric a) y ≤ C N) := by
  classical
  obtain ⟨U, c₀, A, hU, hxU, hclU, hUreg, hc₀, hA, hcurv⟩ :=
    G.exists_curvature_derivative_bounds_of_mem_terminalRegularRegion hx
  obtain ⟨c, hc₀c, hcs⟩ := exists_between hc₀.2
  have hac : a < c := hc₀.1.trans_lt hc₀c
  have hcurv' : ∀ q t, t ∈ _root_.Set.Ico c s → ∀ y ∈ U,
      curvDerivNorm q (G.flow.base.metric t) y ≤ A q :=
    fun q t ht y hy => hcurv q t ⟨hc₀c.le.trans ht.1, ht.2⟩ y hy
  have heq := G.metric_inner_bounds_on_tail ⟨hac.le, hcs⟩ (hA 0) U
    (fun y hy t ht => hcurv' 0 t ht y hy)
  let B₁ := Real.exp (18 * A 0 * (s - c))
  have hB₁ : 1 ≤ B₁ := Real.one_le_exp (by
    exact mul_nonneg (mul_nonneg (by norm_num) (hA 0)) (sub_pos.mpr hcs).le)
  have heq₁ : ∀ t ∈ _root_.Set.Ico c s,
      MetricUniformEquivalentOn U (G.flow.base.metric c) (G.flow.base.metric t) B₁ := by
    intro t ht
    refine ⟨hB₁, fun y hy v => ?_⟩
    have h := heq t ht y hy v
    simpa only [B₁, Real.exp_neg] using h
  obtain ⟨B₀, hB₀, heq₀⟩ := equivOn_compact (I := ThreeModel) isCompact_univ
    (G.flow.base.metric a) (G.flow.base.metric c)
  have heqAll : ∀ t ∈ _root_.Set.Ico c s,
      MetricUniformEquivalentOn U (G.flow.base.metric a) (G.flow.base.metric t) (B₀ * B₁) := by
    intro t ht
    exact MetricUniformEquivalentOn.trans ⟨hB₀, fun y _ v => heq₀ y (_root_.Set.mem_univ y) v⟩ (heq₁ t ht)
  have hB : 1 ≤ B₀ * B₁ := by nlinarith
  obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_between isCompact_singleton hU
    (singleton_subset_iff.mpr hxU)
  have hclK : closure (interior K) ⊆ K := closure_minimal interior_subset hK.isClosed
  have hclU' : closure (interior K) ⊆ U := hclK.trans hKU
  have hjets : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ r ≤ N, ∀ t ∈ _root_.Set.Ico c s, ∀ y ∈ K,
      metricCovDerivNorm r (G.flow.base.metric t) (G.flow.base.metric a) y ≤ C := by
    intro N
    exact G.metric_jet_bounds_of_curvature_derivative_tail hac hK hU hKU
      (G.flow.base.metric a) hB heqAll N A (fun q _ t ht y hy => hcurv' q t ht y hy)
  choose C hC hCb using hjets
  refine ⟨interior K, c, B₀ * B₁, A, C, isOpen_interior, hxK (_root_.Set.mem_singleton x),
    hK.of_isClosed_subset isClosed_closure hclK, hclU'.trans (subset_closure.trans hUreg),
    ⟨hac, hcs⟩, hB, hA, hC, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hB, fun y hy v => (heqAll t ht).2 y (hclU' hy) v⟩
  · intro q t ht y hy
    exact hcurv' q t ht y (hclU' hy)
  · intro N r hr t ht y hy
    exact hCb N r hr t ht y (hclK hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_fixed_reference_metric_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_fixed_reference_metric_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_fixed_reference_metric_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_terminalRegular_fixed_reference_metric_jets

theorem IncomingSlab.eventually_metric_jets_on_compact_regularRegion
    (G : P.IncomingSlab a s) {K : Set P.Carrier} (hK : IsCompact K)
    (hKreg : K ⊆ G.terminalRegularRegion) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in 𝓝[<] s, ∀ r ≤ N, ∀ y ∈ K,
      metricCovDerivNorm r (G.flow.base.metric t) (G.flow.base.metric a) y ≤ C := by
  classical
  have hlocal : ∀ x : K, ∃ (V : Set P.Carrier) (c : ℝ) (C : ℝ),
      IsOpen V ∧ (x : P.Carrier) ∈ V ∧ c < s ∧ 0 ≤ C ∧
      ∀ t ∈ _root_.Set.Ico c s, ∀ r ≤ N, ∀ y ∈ V,
        metricCovDerivNorm r (G.flow.base.metric t) (G.flow.base.metric a) y ≤ C := by
    intro x
    obtain ⟨V, c, B, A, C, hV, hxV, _, _, hc, _, _, hC, _, _, hjets⟩ :=
      G.exists_terminalRegular_fixed_reference_metric_jets (hKreg x.2)
    exact ⟨V, c, C N, hV, hxV, hc.2, hC N,
      fun t ht r hr y hy => hjets N r hr t ht y (subset_closure hy)⟩
  choose V c C hV hxV hcs hC hjets using hlocal
  have hcover : K ⊆ ⋃ x : K, V x := fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover V hV hcover
  refine ⟨∑ x ∈ F, C x, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  have htimes : ∀ᶠ t in 𝓝[<] s, ∀ x ∈ F, t ∈ _root_.Set.Ico (c x) s :=
    (Filter.eventually_all_finset F).mpr (fun x _ => Ico_mem_nhdsLT (hcs x))
  filter_upwards [htimes] with t ht
  intro r hr y hy
  obtain ⟨x, hxF, hyV⟩ := mem_iUnion₂.mp (hF hy)
  exact (hjets x t (ht x hxF) r hr y hyV).trans
    (Finset.single_le_sum (fun x _ => hC x) hxF)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.eventually_metric_jets_on_compact_regularRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.eventually_metric_jets_on_compact_regularRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.eventually_metric_jets_on_compact_regularRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.eventually_metric_jets_on_compact_regularRegion

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
