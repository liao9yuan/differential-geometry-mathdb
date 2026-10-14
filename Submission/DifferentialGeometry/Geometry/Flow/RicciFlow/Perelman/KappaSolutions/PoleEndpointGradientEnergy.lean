import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeLpConvergence
import Submission.DifferentialGeometry.Analysis.Integration.Lp.CompactQuadraticConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientCoefficients
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineWindow

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
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
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

private local instance cotangentNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.cotangentNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.cotangentNormedAddCommGroup target :: scope.openDecls } }

private local instance cotangentNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.cotangentNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.cotangentNormedSpace target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedSpaceRealContinuousLinearMapId_differentialGeometry : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedSpaceRealContinuousLinearMapId_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instNormedSpaceRealContinuousLinearMapId_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instNormedAddCommGroupContinuousLinearMapRealId_differentialGeometry_1 target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instNormedSpaceRealContinuousLinearMapId_differentialGeometry_1 target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

theorem tendsto_integral_poleEndpoint_redLength_gradient_quadratic_unweighted
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
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a' c')) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
      (fderiv ℝ (fun v : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm v.1)) v.2) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let B := fun k (z : E × ℝ) =>
      w z •
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let B₀ := fun z : E × ℝ =>
      w z •
        chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    _root_.Filter.Tendsto (fun k => ∫ z in K ×ˢ _root_.Set.Icc a' c', B k z (d k z) (d k z) ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in K ×ˢ _root_.Set.Icc a' c', B₀ z (d₀ z) (d₀ z) ∂ν)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let d : ℕ → E × ℝ → E →L[ℝ] ℝ := fun k z =>
      (fderiv ℝ (fun v : E × ℝ => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm v.1)) v.2) z).comp
          (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ : E × ℝ → E →L[ℝ] ℝ := fun z =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
  let B := fun k (z : E × ℝ) =>
      w z •
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
  let B₀ := fun z : E × ℝ =>
      w z •
        chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let C : Set (E × ℝ) := K ×ˢ _root_.Set.Icc a' c'
  let T : Set (ℝ × E) := _root_.Set.Icc (1 - c') (1 - a') ×ˢ K
  let r : E × ℝ → ℝ × E := fun z => (1 - z.2, z.1)
  let r' : ℝ × E → E × ℝ := fun z => (z.2, 1 - z.1)
  have hr : Continuous r := (continuous_const.sub continuous_snd).prodMk continuous_fst
  have hr' : Continuous r' := continuous_snd.prodMk (continuous_const.sub continuous_fst)
  have hrC : _root_.Set.MapsTo r C T := by
    intro z hz
    exact ⟨⟨by dsimp [r]; linarith [hz.2.2], by dsimp [r]; linarith [hz.2.1]⟩, hz.1⟩
  have hrT : _root_.Set.MapsTo r' T C := by
    intro z hz
    exact ⟨hz.2, ⟨by dsimp [r']; linarith [hz.1.2],
      by dsimp [r']; linarith [hz.1.1]⟩⟩
  let w' : ℝ × E → ℝ := fun z => w (r' z)
  have hw' : ContinuousOn w' T := hw.comp hr'.continuousOn hrT
  obtain ⟨n, hn⟩ := exists_nat_ge (c' - 1)
  have hwindow : _root_.Set.Icc (1 - c') (1 - a') ⊆ _root_.Set.Icc (-(n : ℝ)) 0 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let cw := (flowMetricConvergenceDataOfHalfLineWindow Phi R bf hsrc htgt
    co.φ co.strictMono co.gInf n (co.convergenceOn n).convergence).restrict Phi hwindow
  have hcwMetric : cw.gInf = co.gInf := rfl
  have hcwIndex : cw.φ = co.φ := rfl
  have hcarrier : _root_.Set.Icc (1 - c') (1 - a') ⊆ (Y).D.carrier := by
    intro t ht
    change t ≤ 0
    linarith [ht.2]
  have hKT : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hTcarrier : T ⊆ (Y).D.carrier ×ˢ K := fun _ hz => ⟨hcarrier hz.1, hz.2⟩
  have hB (k : ℕ) : ContinuousOn (B k) C := by
    let Gk : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
      (lcMetricFamily (I := I) (M := P.M)
        (fun t => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) t)).restrict (Y).D
    have hGk (t : ℝ) : Gk.metric t =
        gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) t := rfl
    have hgram := continuousOn_chartGramOp_gSeqExt
      Phi R bf hsrc htgt (co.φ (rho k)) x hKT
    have h := (Geometry.Curvature.continuousOn_smul_chartGradientBilin
      Gk x (fun z hz => hKT hz.2) (hgram.mono hTcarrier) w' hw').comp
        hr.continuousOn hrC
    simpa only [B, hGk, w', r, r', Function.comp_def, sub_sub_cancel, Prod.eta] using h
  have hB₀ : ContinuousOn B₀ C := by
    have h := (cw.continuousOn_smul_chartGradientBilin
      Phi R bf hsrc htgt (1 - c') (1 - a') x hKT hK hcarrier w' hw').comp
        hr.continuousOn hrC
    simpa only [B₀, hcwMetric, w', r, r', Function.comp_def, sub_sub_cancel, Prod.eta] using h
  have hBconv : TendstoUniformlyOn B B₀ _root_.Filter.atTop C := by
    have h := ((cw.tendstoUniformlyOn_smul_chartGradientBilin
      Phi R bf hsrc htgt (1 - c') (1 - a') x hKT hK hcarrier w' hw').comp r).mono hrC
    simpa only [B, B₀, hcwMetric, hcwIndex, w', r, r', Function.comp_def,
      sub_sub_cancel, Prod.eta] using
      h.seq_tendstoUniformlyOn rho hrho
  obtain ⟨N, hd, hd₀, hstrong⟩ := exists_tendsto_toLp_fderiv_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc 2 (by norm_num)
  apply (_root_.Filter.tendsto_add_atTop_iff_nat N).mp
  exact tendsto_setIntegral_quadratic_of_tendstoUniformlyOn_of_isCompact
    (μ := ν) (hK.prod _root_.CompactIccSpace.isCompact_Icc) (fun k => B (k + N)) B₀
    (fun k => hB (k + N)) hB₀
    (hBconv.seq_tendstoUniformlyOn (fun k => k + N) (_root_.Filter.tendsto_add_atTop_nat N))
    (fun k => d (k + N)) d₀ hd hd₀ hstrong

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_gradient_quadratic_unweighted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_gradient_quadratic_unweighted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_gradient_quadratic_unweighted ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_gradient_quadratic_unweighted

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
