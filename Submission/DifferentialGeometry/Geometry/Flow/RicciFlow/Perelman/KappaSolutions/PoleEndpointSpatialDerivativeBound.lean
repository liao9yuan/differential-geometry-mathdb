import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.CompactSpatialBound
import Submission.DifferentialGeometry.Geometry.Metric.SmoothMapLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instTopologicalSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instChartedSpaceM_3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instIsManifoldRealSomeENatTopM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpace_differentialGeometry target :: scope.openDecls } }

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in _root_.Filter.atTop, ∀ v ∈ K, ∀ t ∈ _root_.Set.Icc a c,
      ‖(fderiv ℝ (fun z : E × ℝ =>
        redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2) (v, t)).comp
            (ContinuousLinearMap.inl ℝ E ℝ)‖ ≤ B := by
  obtain ⟨C, Dt, hC, _hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmodulus
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : _root_.Bundle.RiemannianBundle (TangentSpace I : P.M → Type _) := ⟨R.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : P.M → Type _) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let _ : PseudoEMetricSpace P.M := PseudoEMetricSpace.ofRiemannianMetric I P.M
  have hedist (y w : P.M) : _root_.EDist.edist y w = riemannianEDistOf R y w :=
    IsRiemannianManifold.out (I := I) y w
  have hchart : LocallyLipschitzOn W (extChartAt I x).symm := by
    intro v hv
    have hdiff : ContMDiffWithinAt 𝓘(ℝ, E) I 1
        (extChartAt I x).symm (_root_.Set.range I) v :=
      contMDiffWithinAt_extChartAt_symm_range x (hWt hv)
    obtain ⟨L, V, hV, hLV⟩ := hdiff.exists_lipschitzOnWith I.convex_range
    exact ⟨L, V, nhdsWithin_mono v (hWt.trans (extChartAt_target_subset_range x)) hV, hLV⟩
  obtain ⟨B, hB, hbound⟩ :=
    Analysis.Calculus.exists_norm_fderiv_comp_inl_le_of_edist_bound
      hW hK hKW hchart hWJ
      (fun k : {k : ℕ // N ≤ k} => fun z : P.M × ℝ =>
        redLength ((U).term (phi (co.φ k.1))).S 0 p (Phi.map (co.φ k.1) z.1) z.2)
      hC zero_lt_one (by
        intro k y hy w hw t ht hdist
        simpa only [Real.dist_eq, hedist, sub_self, abs_zero, _root_.MulZeroClass.mul_zero, add_zero] using
          hN k.1 k.2 y hy w hw t ht t ht hdist)
  refine ⟨B, hB, ?_⟩
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
  exact hbound ⟨k, hk⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le

theorem eventually_memLp_fderiv_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    (μ : _root_.MeasureTheory.Measure (E × ℝ)) [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict (K ×ˢ _root_.Set.Icc a c))]
    (pExp : ℝ≥0∞) :
    ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.MemLp (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ =>
        redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z).comp
            (ContinuousLinearMap.inl ℝ E ℝ)) pExp (μ.restrict (K ×ˢ _root_.Set.Icc a c)) := by
  obtain ⟨B, _hB, hbound⟩ :=
    exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
      x hW hK hKW hWt hWJ
  filter_upwards [hbound] with k hk
  have hm : Measurable (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ =>
        redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z).comp
            (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).continuous.measurable).comp
        (measurable_fderiv ℝ _)
  apply MemLp.of_bound hm.aestronglyMeasurable B
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz
  exact hk z.1 hz.1 z.2 hz.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_memLp_fderiv_poleEndpoint_redLength_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_memLp_fderiv_poleEndpoint_redLength_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_memLp_fderiv_poleEndpoint_redLength_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_memLp_fderiv_poleEndpoint_redLength_chart

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem memLp_fderiv_poleEndpoint_redLength_limit_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    (μ : _root_.MeasureTheory.Measure (E × ℝ)) [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict (K ×ˢ _root_.Set.Icc a c))]
    (pExp : ℝ≥0∞) :
    _root_.MeasureTheory.MemLp (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) pExp (μ.restrict (K ×ˢ _root_.Set.Icc a c)) := by
  obtain ⟨C, Dt, hC, _hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  have hlim : ∀ y ∈ J, ∀ w ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      riemannianEDistOf R y w < ENNReal.ofReal 1 →
      |ell (y, t) - ell (w, t)| ≤ C * (riemannianEDistOf R y w).toReal := by
    intro y hy w hw t ht hdist
    apply le_of_tendsto ((hconv y hy t ht).sub (hconv w hw t ht)).abs
    filter_upwards [hrho.eventually hmodulus] with k hk
    simpa only [sub_self, abs_zero, _root_.MulZeroClass.mul_zero, add_zero] using
      hk y hy w hw t ht t ht hdist
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : _root_.Bundle.RiemannianBundle (TangentSpace I : P.M → Type _) := ⟨R.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : P.M → Type _) :=
    ⟨R.inner, R.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let _ : PseudoEMetricSpace P.M := PseudoEMetricSpace.ofRiemannianMetric I P.M
  have hedist (y w : P.M) : _root_.EDist.edist y w = riemannianEDistOf R y w :=
    IsRiemannianManifold.out (I := I) y w
  have hchart : LocallyLipschitzOn W (extChartAt I x).symm := by
    intro v hv
    have hdiff : ContMDiffWithinAt 𝓘(ℝ, E) I 1
        (extChartAt I x).symm (_root_.Set.range I) v :=
      contMDiffWithinAt_extChartAt_symm_range x (hWt hv)
    obtain ⟨L, V, hV, hLV⟩ := hdiff.exists_lipschitzOnWith I.convex_range
    exact ⟨L, V, nhdsWithin_mono v (hWt.trans (extChartAt_target_subset_range x)) hV, hLV⟩
  obtain ⟨B, _hB, hbound⟩ :=
    Analysis.Calculus.exists_norm_fderiv_comp_inl_le_of_edist_bound
      hW hK hKW hchart hWJ (fun _ : Unit => ell) hC zero_lt_one (by
        intro _ y hy w hw t ht hdist
        simpa only [Real.dist_eq, hedist] using hlim y hy w hw t ht hdist)
  have hm : Measurable (fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)) :=
    (((ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ).flip
      (ContinuousLinearMap.inl ℝ E ℝ)).continuous.measurable).comp
        (measurable_fderiv ℝ _)
  apply MemLp.of_bound hm.aestronglyMeasurable B
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz
  exact hbound () z.1 hz.1 z.2 hz.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.memLp_fderiv_poleEndpoint_redLength_limit_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.memLp_fderiv_poleEndpoint_redLength_limit_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.memLp_fderiv_poleEndpoint_redLength_limit_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.memLp_fderiv_poleEndpoint_redLength_limit_chart

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
