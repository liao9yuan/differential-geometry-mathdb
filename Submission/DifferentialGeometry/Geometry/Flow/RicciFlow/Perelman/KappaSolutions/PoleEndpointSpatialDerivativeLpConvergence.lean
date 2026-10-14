import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeBound
import Submission.DifferentialGeometry.Analysis.Integration.Lp.CovectorConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

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

namespace HalfLineMetricConvergenceData

theorem exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (pExp : ℝ≥0∞) [Fact (1 ≤ pExp)] (hpExp : pExp ≠ (⊤ : ℝ≥0∞)) :
    let μ :=
      ((DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)).restrict (K ×ˢ _root_.Set.Icc a' c')
    let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
      (fderiv ℝ (fun w : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm w.1)) w.2) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
      (fderiv ℝ (fun w : E × ℝ => ell ((extChartAt I x).symm w.1, w.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    ∃ N : ℕ, ∃ hd : ∀ k, _root_.MeasureTheory.MemLp (d (k + N)) pExp μ, ∃ hd₀ : _root_.MeasureTheory.MemLp d₀ pExp μ,
      Tendsto (fun k => (hd k).toLp (d (k + N))) _root_.Filter.atTop (𝓝 (hd₀.toLp d₀)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let μ := ν.restrict (K ×ˢ _root_.Set.Icc a' c')
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (hK.prod _root_.CompactIccSpace.isCompact_Icc).measure_ne_top
  let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
    (fderiv ℝ (fun w : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm w.1)) w.2) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
    (fderiv ℝ (fun w : E × ℝ => ell ((extChartAt I x).symm w.1, w.2)) z).comp
      (ContinuousLinearMap.inl ℝ E ℝ)
  have ha' : 1 ≤ a' := (ha.trans haa).le
  have hinterval : _root_.Set.Icc a' c' ⊆ _root_.Set.Icc a c := fun _ ht =>
    ⟨haa.le.trans ht.1, ht.2.trans hcc.le⟩
  have hmem : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.MemLp (d k) pExp μ := by
    exact hrho.eventually (eventually_memLp_fderiv_poleEndpoint_redLength_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha' hbase
      x hW hK hKW hWt hWJ ν pExp)
  have hmem₀ : _root_.MeasureTheory.MemLp d₀ pExp μ :=
    memLp_fderiv_poleEndpoint_redLength_limit_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha' hbase
      rho hrho ell (fun y hy t ht => hconv y hy t (hinterval ht))
      x hW hK hKW hWt hWJ ν pExp
  obtain ⟨B, _hB, hbound⟩ := exists_eventually_norm_fderiv_poleEndpoint_redLength_chart_le
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c') ha' hbase
    x hW hK hKW hWt hWJ
  have hbound' : ∀ᶠ k in _root_.Filter.atTop, ∀ᵐ z ∂μ, ‖d k z‖ ≤ B := by
    filter_upwards [hrho.eventually hbound] with k hk
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz
    exact hk z.1 hz.1 z.2 hz.2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmem.and hbound')
  let hd : ∀ k, _root_.MeasureTheory.MemLp (d (k + N)) pExp μ := fun k =>
    (hN (k + N) (Nat.le_add_left N k)).1
  refine ⟨N, hd, hmem₀, ?_⟩
  apply MemLp.tendsto_toLp_of_ae_tendsto_apply_of_ae_norm_le hpExp
    (fun k => d (k + N)) d₀ hd hmem₀
    (fun k => (hN (k + N) (Nat.le_add_left N k)).2)
  have hae := ae_tendsto_fderiv_poleEndpoint_redLength_chart_apply
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hWt hWJ
  filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae hae,
    _root_.MeasureTheory.ae_restrict_mem (hK.measurableSet.prod measurableSet_Icc)] with z hz hzs
  intro v
  exact (hz ⟨hKW hzs.1, haa.trans_le hzs.2.1, hzs.2.2.trans_lt hcc⟩ v).comp
    (_root_.Filter.tendsto_add_atTop_nat N)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
