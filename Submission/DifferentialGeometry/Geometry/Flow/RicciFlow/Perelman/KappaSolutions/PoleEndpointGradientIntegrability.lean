import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSpatialDerivativeBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientCoefficients
import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineWindow

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.MeasureTheory _root_.Submission.MeasureTheory
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

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorNormedSpace target :: scope.openDecls } }

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorDualNormedSpace target :: scope.openDecls } }

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedAddCommGroup target :: scope.openDecls } }

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.covectorBilinNormedSpace target :: scope.openDecls } }

omit [I.Boundaryless] in
private theorem integrableOn_reflected_chartGradientBilin
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    {Dg : RealTimeInterval} (G : MetricConnectionFamilyOn (I := I) (M := N) Dg)
    (x : N) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x).target)
    {a c : ℝ}
    (hG : ContinuousOn (chartGramOp G x) (_root_.Set.Icc (1 - c) (1 - a) ×ˢ K))
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c))
    (d : E × ℝ → E →L[ℝ] ℝ) (μ : _root_.MeasureTheory.Measure (E × ℝ))
    (hd : _root_.MeasureTheory.MemLp d 2 (μ.restrict (K ×ˢ _root_.Set.Icc a c))) :
    _root_.MeasureTheory.IntegrableOn (fun z =>
      (w z • chartGradientBilin (G.metric (1 - z.2)) x
        ((extChartAt I x).symm z.1)) (d z) (d z)) (K ×ˢ _root_.Set.Icc a c) μ := by
  let C := K ×ˢ _root_.Set.Icc a c
  let T := _root_.Set.Icc (1 - c) (1 - a) ×ˢ K
  let r : E × ℝ → ℝ × E := fun z => (1 - z.2, z.1)
  let r' : ℝ × E → E × ℝ := fun z => (z.2, 1 - z.1)
  let w' : ℝ × E → ℝ := fun z => w (r' z)
  let B := fun z : E × ℝ =>
    w z • chartGradientBilin (G.metric (1 - z.2)) x ((extChartAt I x).symm z.1)
  have hr : Continuous r := (continuous_const.sub continuous_snd).prodMk continuous_fst
  have hr' : Continuous r' := continuous_snd.prodMk (continuous_const.sub continuous_fst)
  have hrC : _root_.Set.MapsTo r C T := by
    intro z hz
    exact ⟨⟨by dsimp [r]; linarith [hz.2.2],
      by dsimp [r]; linarith [hz.2.1]⟩, hz.1⟩
  have hrT : _root_.Set.MapsTo r' T C := by
    intro z hz
    exact ⟨hz.2, ⟨by dsimp [r']; linarith [hz.1.2],
      by dsimp [r']; linarith [hz.1.1]⟩⟩
  have hw' : ContinuousOn w' T := hw.comp hr'.continuousOn hrT
  have hB : ContinuousOn B C := by
    have hb := (Geometry.Curvature.continuousOn_smul_chartGradientBilin
      G x (fun z hz => hKt hz.2) hG w' hw').comp hr.continuousOn hrC
    simpa only [B, w', r, r', Function.comp_def, sub_sub_cancel, Prod.eta] using hb
  have hC : IsCompact C := hK.prod _root_.CompactIccSpace.isCompact_Icc
  obtain ⟨L, hL⟩ := hC.exists_bound_of_continuousOn hB
  apply MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable B (C := L) ?_ ?_ hd hd
  · intro u v
    have heval : ContinuousOn (fun z => B z u v) C :=
      (hB.clm_apply continuousOn_const).clm_apply continuousOn_const
    exact heval.aestronglyMeasurable_of_subset_isCompact hC hC.measurableSet Subset.rfl
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    exact hL z hz

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.integrableOn_reflected_chartGradientBilin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.integrableOn_reflected_chartGradientBilin target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

theorem eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic
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
    (x : P.M) {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    (μ : _root_.MeasureTheory.Measure (E × ℝ)) [_root_.MeasureTheory.IsFiniteMeasure (μ.restrict (K ×ˢ _root_.Set.Icc a c))]
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    ∀ᶠ k in _root_.Filter.atTop,
      let d := fun z : E × ℝ =>
        (fderiv ℝ (fun v : E × ℝ =>
          redLength ((U).term (phi (co.φ (rho k)))).S 0 p
            (Phi.map (co.φ (rho k)) ((extChartAt I x).symm v.1)) v.2) z).comp
              (ContinuousLinearMap.inl ℝ E ℝ)
      _root_.MeasureTheory.IntegrableOn (fun z =>
        (w z • chartGradientBilin
          (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
            ((extChartAt I x).symm z.1)) (d z) (d z)) (K ×ˢ _root_.Set.Icc a c) μ := by
  have hmem := eventually_memLp_fderiv_poleEndpoint_redLength_chart (c := c)
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    x hW hK hKW hWt hWJ μ 2
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hcarrier : _root_.Set.Icc (1 - c) (1 - a) ⊆ (Y).D.carrier := by
    intro t ht
    change t ≤ 0
    linarith only [ht.2, ha]
  filter_upwards [hrho.eventually hmem] with k hk
  let Gk : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) t)).restrict (Y).D
  have hgram : ContinuousOn (chartGramOp Gk x) (_root_.Set.Icc (1 - c) (1 - a) ×ˢ K) :=
    (continuousOn_chartGramOp_gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) x hKt).mono
      (fun z hz => ⟨hcarrier hz.1, hz.2⟩)
  exact integrableOn_reflected_chartGradientBilin Gk x hK hKt hgram w hw _ μ hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic

theorem integrableOn_poleEndpoint_redLength_limit_gradient_quadratic
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
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let d₀ := fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    _root_.MeasureTheory.IntegrableOn (fun z =>
      (w z • chartGradientBilin (co.gInf (1 - z.2)) x
        ((extChartAt I x).symm z.1)) (d₀ z) (d₀ z)) (K ×ˢ _root_.Set.Icc a c) μ := by
  have hmem := memLp_fderiv_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hW hK hKW hWt hWJ μ 2
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  obtain ⟨n, hn⟩ := exists_nat_ge (c - 1)
  have hwindow : _root_.Set.Icc (1 - c) (1 - a) ⊆ _root_.Set.Icc (-(n : ℝ)) 0 := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2, hn, ha]
  let cw := (flowMetricConvergenceDataOfHalfLineWindow Phi R bf hsrc htgt
    co.φ co.strictMono co.gInf n (co.convergenceOn n).convergence).restrict Phi hwindow
  have hcarrier : _root_.Set.Icc (1 - c) (1 - a) ⊆ (Y).D.carrier := by
    intro t ht
    change t ≤ 0
    linarith only [ht.2, ha]
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) (Y).D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict (Y).D
  have hgram : ContinuousOn (chartGramOp GInf x) (_root_.Set.Icc (1 - c) (1 - a) ×ˢ K) :=
    cw.continuousOn_chartGramOp Phi R bf hsrc htgt (1 - c) (1 - a) x hKt hK hcarrier
  exact integrableOn_reflected_chartGradientBilin GInf x hK hKt hgram w hw _ μ hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_gradient_quadratic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_gradient_quadratic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_gradient_quadratic ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_gradient_quadratic

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
