import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalChartJets
import Submission.DifferentialGeometry.Geometry.Operator.Family.Gram.Smoothness
import Submission.DifferentialGeometry.Analysis.Calculus.IteratedDerivative.SpaceJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

private theorem continuousWithinAt_terminal_of_uniform
    {Y Z : Type*} [TopologicalSpace Y] [PseudoMetricSpace Z]
    {F : ℝ → Y → Z} {W : Set Y} {b : ℝ} {y : Y}
    (hF : TendstoUniformlyOn F (F b) (𝓝[<] b) W)
    (hcont : ContinuousWithinAt (F b) W y) :
    ContinuousWithinAt (fun q : ℝ × Y => F q.1 q.2) (_root_.Set.Iic b ×ˢ W) (b, y) := by
  rw [ContinuousWithinAt, nhdsWithin_prod_eq, Metric.tendsto_nhds]
  intro ε hε
  have hclose : ∀ᶠ t in 𝓝[<] b, ∀ z ∈ W, _root_.Dist.dist (F t z) (F b z) < ε / 2 := by
    have h := Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) (half_pos hε)
    exact h.mono fun t ht z hz => by simpa only [dist_comm] using ht z hz
  have hcloseLE : ∀ᶠ t in 𝓝[≤] b, ∀ z ∈ W, _root_.Dist.dist (F t z) (F b z) < ε / 2 := by
    rw [← _root_.Set.Iio_insert, nhdsWithin_insert, _root_.Filter.eventually_sup, _root_.Filter.eventually_pure]
    exact ⟨fun z _ => by simpa only [dist_self] using half_pos hε, hclose⟩
  have hsmall : ∀ᶠ z in 𝓝[W] y, _root_.Dist.dist (F b z) (F b y) < ε / 2 :=
    Metric.tendsto_nhds.mp hcont (ε / 2) (half_pos hε)
  filter_upwards [hcloseLE.prod_mk (hsmall.and self_mem_nhdsWithin)] with q hq
  exact (dist_triangle (F q.1 q.2) (F b q.2) (F b y)).trans_lt
    ((add_lt_add (hq.1 q.2 hq.2.2) hq.2.1).trans_eq (add_halves ε))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.continuousWithinAt_terminal_of_uniform
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.continuousWithinAt_terminal_of_uniform target :: scope.openDecls } }

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

local instance terminalJointSpatialJetsC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC1
local instance terminalJointSpatialJetsC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.terminalJointSpatialJetsC2

private theorem chartGram_jets_tendsto_terminal_near_chart_point
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : _root_.Set.Icc a b ⊆ D.carrier)
    (hreg : _root_.Set.Ioo a b ⊆ D.regular) (p x : M) (hxchart : x ∈ (chartAt H p).source) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I p x ∈ W ∧ W ⊆ (extChartAt I p).target ∧
      ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
        TendstoUniformlyOn (fun t => iteratedFDeriv ℝ r
          (chartGramOnE (I := I) (S.base.metric t) p i j))
          (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric b) p i j)) (𝓝[<] b) W := by
  classical
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨V, c, L, hV, hxV, _, _, hcb, hL, hlip⟩ :=
    exists_local_metric_time_lipschitz_before_terminal S hS hab hslab hreg x
  obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_between isCompact_singleton
    (hV.inter (chartAt H p).open_source) (singleton_subset_iff.mpr ⟨hxV, hxchart⟩)
  have hKchart : K ⊆ (chartAt H p).source := fun z hz => (hKV hz).2
  let W : Set E := (extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' interior K
  have hW : IsOpen W := (continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := I) p) isOpen_interior
  have hxsource : x ∈ (extChartAt I p).source := by simpa only [extChartAt_source] using hxchart
  have hxW : extChartAt I p x ∈ W := by
    refine ⟨(extChartAt I p).map_source hxsource, ?_⟩
    change (extChartAt I p).symm (extChartAt I p x) ∈ interior K
    rw [(extChartAt I p).left_inv hxsource]
    exact hxK (_root_.Set.mem_singleton x)
  refine ⟨W, hW, hxW, fun _ hz => hz.1, ?_⟩
  intro r i j
  have hcauchy (q : ℕ) : UniformCauchySeqOn (fun t => iteratedFDeriv ℝ q
      (chartGramOnE (I := I) (S.base.metric t) p i j)) (𝓝[<] b) W := by
    obtain ⟨C, hC, hchart⟩ := chartJet_sub_le (I := I) (S.base.metric c) p hK hKchart q
    let B : ℝ≥0 := ⟨C * ∑ k ∈ Finset.range (q + 1), L k,
      mul_nonneg hC (Finset.sum_nonneg fun k _ => hL k)⟩
    apply uniformCauchySeqOn_nhdsLT_of_lipschitzOnWith hcb _ W B
    intro y hy
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    let z := (extChartAt I p).symm y
    have hzK : z ∈ K := interior_subset hy.2
    have hzy : extChartAt I p z = y := (extChartAt I p).right_inv hy.1
    rw [dist_eq_norm, Real.dist_eq]
    have hsum : (∑ k ∈ Finset.range (q + 1),
        metricDerivNorm (I := I) k (S.base.metric s) (S.base.metric t) (S.base.metric c) z)
        ≤ (∑ k ∈ Finset.range (q + 1), L k) * |s - t| := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k _ => hlip k s ⟨hs.1.le, hs.2⟩
        t ⟨ht.1.le, ht.2⟩ z (subset_closure (hKV hzK).1)
    have hh := (hchart (S.base.metric s) (S.base.metric t) z hzK i j).trans
      (mul_le_mul_of_nonneg_left hsum hC)
    change _ ≤ (C * ∑ k ∈ Finset.range (q + 1), L k) * |s - t|
    simpa only [hzy, mul_assoc] using hh
  apply tendstoUniformlyOn_iteratedFDeriv_of_uniformCauchySeqOn hW
    (fun t => chartGramOnE (I := I) (S.base.metric t) p i j)
    (chartGramOnE (I := I) (S.base.metric b) p i j) r
    (fun t => (chartGramOnE_contDiffOn (I := I) (S.base.metric t) p i j).mono
      (fun _ hy => hy.1)) (fun q _ => hcauchy q) ?_ r le_rfl
  intro y _
  have hnear : ∀ᶠ t in 𝓝[<] b, t ∈ _root_.Set.Ioo a b := Ioo_mem_nhdsLT hab
  have htime : _root_.Filter.Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝[D.carrier] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds,
      hnear.mono fun t ht => hslab ⟨ht.1.le, ht.2.le⟩⟩
  simpa only [chartGramOnE, chartGramMatrix_apply, Function.comp_def, SolutionOn.family] using
    (hS.smoothMetric.coeff_cont ((extChartAt I p).symm y)
      (chartBasisVecFiber (I := I) p i ((extChartAt I p).symm y))
      (chartBasisVecFiber (I := I) p j ((extChartAt I p).symm y))
      b (hslab ⟨hab.le, le_rfl⟩)).tendsto.comp htime

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.chartGram_jets_tendsto_terminal_near_chart_point
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.chartGram_jets_tendsto_terminal_near_chart_point target :: scope.openDecls } }

theorem solution_chartGram_jets_continuousOn_closed
    [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ioo a b ⊆ D.regular) (p : M) :
    ∀ r : ℕ, ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ r
        (chartGramOnE (I := I) (S.base.metric q.1) p i j) q.2)
        (_root_.Set.Icc c b ×ˢ (extChartAt I p).target) := by
  intro r i j
  rintro ⟨t, y⟩ ⟨ht, hy⟩
  by_cases htb : t = b
  · subst t
    have hxchart : (extChartAt I p).symm y ∈ (chartAt H p).source := by
      simpa only [extChartAt_source] using (extChartAt I p).map_target hy
    obtain ⟨W, hW, hyW, _, hlim⟩ := chartGram_jets_tendsto_terminal_near_chart_point
      S hS (hac.trans hcb) hslab hreg p ((extChartAt I p).symm y) hxchart
    rw [(extChartAt I p).right_inv hy] at hyW
    have hspatial : ContinuousAt
        (iteratedFDeriv ℝ r (chartGramOnE (I := I) (S.base.metric b) p i j)) y :=
      ((chartGramOnE_contDiffOn (I := I) (S.base.metric b) p i j).contDiffAt
        ((isOpen_extChartAt_target (I := I) p).mem_nhds hy)).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)
    have hlocal := continuousWithinAt_terminal_of_uniform (hlim r i j)
      hspatial.continuousWithinAt
    have hfull : ContinuousWithinAt (fun q : ℝ × E => iteratedFDeriv ℝ r
        (chartGramOnE (I := I) (S.base.metric q.1) p i j) q.2)
        (_root_.Set.Iic b ×ˢ (_root_.Set.univ : Set E)) (b, y) := by
      simpa only [ContinuousWithinAt, nhdsWithin_prod_eq, nhdsWithin_univ,
        nhdsWithin_eq_nhds.mpr (hW.mem_nhds hyW)] using hlocal
    exact hfull.mono (fun q hq => ⟨hq.1.2, _root_.Set.mem_univ _⟩)
  · have htreg : t ∈ D.regular := hreg ⟨hac.trans_le ht.1, lt_of_le_of_ne ht.2 htb⟩
    have hyint : y ∈ interior (extChartAt I p).target :=
      (isOpen_extChartAt_target (I := I) p).interior_eq.symm ▸ hy
    have hsmooth : ContDiffAt ℝ ∞
        (fun q : ℝ × E => chartGramOnE (I := I) (S.base.metric q.1) p i j q.2) (t, y) :=
      (MetricFamilySmoothOn.chartGramOnE_contDiffOn (I := I) (g_fam := S.family.metric)
        hS.smoothMetric (J := D.regular) (fun _ h => h) p i j).contDiffAt
          ((D.regular_isOpen.prod isOpen_interior).mem_nhds ⟨htreg, hyint⟩)
    exact (DifferentialGeometry.Analysis.spaceJet_contAt hsmooth r
      (by exact_mod_cast le_top)).continuousWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.solution_chartGram_jets_continuousOn_closed

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
