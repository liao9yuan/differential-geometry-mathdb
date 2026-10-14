import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.LocallyLipschitz

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

theorem locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
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
    (x : P.M) {W : Set E} (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J) :
    LocallyLipschitzOn (_root_.Set.Icc a c ×ˢ W)
      (fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)) := by
  have hlip := locallyLipschitzOn_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hWt hWJ
  have hswap : LipschitzWith 1 (Prod.swap : ℝ × E → E × ℝ) := by
    intro u v
    simp only [Prod.edist_eq, Prod.fst_swap, Prod.snd_swap, ENNReal.coe_one, one_mul]
    exact le_of_eq (max_comm _ _)
  have hmap : _root_.Set.MapsTo (Prod.swap : ℝ × E → E × ℝ)
      (_root_.Set.Icc a c ×ˢ W) (W ×ˢ _root_.Set.Icc a c) := fun _ hz => ⟨hz.2, hz.1⟩
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hlip.restrict.comp (hswap.lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart

theorem ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice
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
    (x : P.M) {W : Set E} (hW : MeasurableSet W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a ≤ a') (hcc : c' ≤ c) :
    ∀ᵐ y ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).restrict W,
      LocallyLipschitzOn (_root_.Set.Icc a' c')
        (fun t : ℝ => ell ((extChartAt I x).symm y, t)) := by
  have hlip := locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hWt hWJ
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hW] with y hy
  have hmap : _root_.Set.MapsTo (fun t : ℝ => (t, y)) (_root_.Set.Icc a' c') (_root_.Set.Icc a c ×ˢ W) := by
    intro t ht
    exact ⟨⟨haa.trans ht.1, ht.2.trans hcc⟩, hy⟩
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hlip.restrict.comp
    ((LipschitzWith.prodMk_right y).lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_locallyLipschitzOn_poleEndpoint_redLength_limit_time_slice

theorem ae_differentiableAt_poleEndpoint_redLength_limit_slices
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
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c) :
    ∀ᵐ z ∂(volume.restrict (_root_.Set.Ioc a' c')).prod
        ((DifferentialGeometry.Integral.Measure.modelHaar (E := E)).restrict W),
      DifferentiableAt ℝ (fun t : ℝ => ell ((extChartAt I x).symm z.2, t)) z.1 ∧
      DifferentiableAt ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2 := by
  have hlip := locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hWt hWJ
  have hopen : LocallyLipschitzOn (_root_.Set.Ioo a c ×ˢ W)
      (fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)) :=
    hlip.mono fun _ hz => ⟨⟨hz.1.1.le, hz.1.2.le⟩, hz.2⟩
  have hdiff := hopen.ae_differentiableAt_of_isOpen
    (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod
      (DifferentialGeometry.Integral.Measure.modelHaar (E := E)))
    (isOpen_Ioo.prod hW)
  rw [Measure.prod_restrict]
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae hdiff,
    _root_.MeasureTheory.ae_restrict_mem (measurableSet_Ioc.prod hW.measurableSet)] with z hz hzs
  have hzO : z ∈ _root_.Set.Ioo a c ×ˢ W :=
    ⟨⟨haa.trans hzs.1.1, hzs.1.2.trans_lt hcc⟩, hzs.2⟩
  have hd : DifferentiableAt ℝ
      (fun v : ℝ × E => ell ((extChartAt I x).symm v.2, v.1)) z := hz hzO
  have ht := hd.comp z.1 (show DifferentiableAt ℝ (fun t : ℝ => (t, z.2)) z.1 from
    differentiableAt_id.prodMk (differentiableAt_const z.2))
  have hs := hd.comp z.2 (show DifferentiableAt ℝ (fun y : E => (z.1, y)) z.2 from
    (differentiableAt_const z.1).prodMk differentiableAt_id)
  exact ⟨ht, hs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_slices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_slices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_slices ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_slices

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
