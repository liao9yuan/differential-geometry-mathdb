import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthContinuity
import Submission.DifferentialGeometry.Analysis.Integration.Integral.DominatedConvergence
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedCostBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
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

private theorem integrable_limit_and_integral_convergence
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : _root_.Set.MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    _root_.MeasureTheory.IntegrableOn (fun z => w z * ell ((extChartAt I x).symm z.1, z.2))
      (K ×ˢ _root_.Set.Icc a c) ν ∧
    _root_.Filter.Tendsto (fun k => ∫ z in K ×ˢ _root_.Set.Icc a c, w z *
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2 ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in K ×ˢ _root_.Set.Icc a c, w z * ell ((extChartAt I x).symm z.1, z.2) ∂ν)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ _root_.Set.Icc a c
  let f : ℕ → E × ℝ → ℝ := fun k z =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  have hC : IsCompact C := hK.prod _root_.CompactIccSpace.isCompact_Icc
  have hcoord : ContinuousOn
      (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2)) C :=
    (((continuousOn_extChartAt_symm x).mono hKt).comp continuous_fst.continuousOn
      (fun _ hz => hz.1)).prodMk continuous_snd.continuousOn
  have hcoordJ : _root_.Set.MapsTo (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2))
      C (J ×ˢ _root_.Set.Icc a c) := fun _ hz => ⟨hKJ hz.1, hz.2⟩
  have hcontinuous := eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
  have hmeas : ∀ᶠ k in _root_.Filter.atTop,
      AEStronglyMeasurable (fun z => w z * f k z) (ν.restrict C) := by
    filter_upwards [hrho.eventually hcontinuous] with k hk
    have hf : ContinuousOn (f k) C := by
      simpa only [f, Function.comp_def] using hk.comp hcoord hcoordJ
    exact (hw.mul hf).aestronglyMeasurable hC.measurableSet
  obtain ⟨V, _hV, hupper⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase
  have hnonneg (k : ℕ) (z : E × ℝ) (hz : z ∈ C) : 0 ≤ f k z := by
    obtain ⟨B, hB⟩ := (hancient (phi (co.φ (rho k)))).globalScalarBound
    have hscalar : ∀ s ∈ _root_.Set.Icc 0 z.2, ∀ y,
        0 ≤ ((U).term (phi (co.φ (rho k)))).S.scalar (0 - s) y := by
      intro s hs y
      have hmem : -s ∈ ancientTimeInterval.carrier := by
        rw [ancientTimeInterval_carrier]
        exact Set.mem_Iic.mpr (by linarith [hs.1])
      simpa only [zero_sub] using (hB (-s) hmem y).1
    change 0 ≤ lCost ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2 /
        (2 * Real.sqrt z.2)
    exact div_nonneg
      (lCost_nonneg_of_scalar_nonneg _ 0 (ha.trans_le hz.2.1).le hscalar _ _)
      (by positivity)
  have hbound : ∀ᶠ k in _root_.Filter.atTop, ∀ᵐ z ∂ν.restrict C,
      ‖w z * f k z‖ ≤ ‖w z‖ * V := by
    filter_upwards [hrho.eventually hupper] with k hk
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    rw [norm_mul, Real.norm_of_nonneg (hnonneg k z hz)]
    exact mul_le_mul_of_nonneg_left
      (hk _ (hKJ hz.1) _ hz.2) (norm_nonneg _)
  have hintegrable : _root_.MeasureTheory.Integrable (fun z => ‖w z‖ * V) (ν.restrict C) :=
    (hw.norm.mul continuousOn_const).integrableOn_compact hC
  have hlimit : ∀ᵐ z ∂ν.restrict C,
      Tendsto (fun k => w z * f k z) _root_.Filter.atTop (𝓝 (w z * f₀ z)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    exact tendsto_const_nhds.mul (hconv _ (hKJ hz.1) _ hz.2)
  exact ⟨integrable_of_dominated_convergence
    (fun z => ‖w z‖ * V) hmeas hbound hintegrable hlimit,
    _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖w z‖ * V) hmeas hbound hintegrable hlimit⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_limit_and_integral_convergence
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_limit_and_integral_convergence target :: scope.openDecls } }

theorem tendsto_integral_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : _root_.Set.MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    _root_.Filter.Tendsto (fun k => ∫ z in K ×ˢ _root_.Set.Icc a c, w z *
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2 ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in K ×ˢ _root_.Set.Icc a c, w z * ell ((extChartAt I x).symm z.1, z.2) ∂ν)) := by
  exact (integrable_limit_and_integral_convergence
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hK hKt hKJ w hw).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_redLength_chart

theorem integrableOn_poleEndpoint_redLength_limit_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : _root_.Set.MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    _root_.MeasureTheory.IntegrableOn (fun z => w z * ell ((extChartAt I x).symm z.1, z.2))
      (K ×ˢ _root_.Set.Icc a c) ν := by
  exact (integrable_limit_and_integral_convergence
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha hbase
    rho hrho ell hconv x hK hKt hKJ w hw).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_redLength_limit_chart

theorem eventually_integrableOn_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 0 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (hKJ : _root_.Set.MapsTo (extChartAt I x).symm K J)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (fun z : E × ℝ => w z *
      redLength ((U).term (phi (co.φ k))).S 0 p
        (Phi.map (co.φ k) ((extChartAt I x).symm z.1)) z.2) (K ×ˢ _root_.Set.Icc a c) ν := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  have hcoord : ContinuousOn
      (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2)) (K ×ˢ _root_.Set.Icc a c) :=
    (((continuousOn_extChartAt_symm x).mono hKt).comp continuous_fst.continuousOn
      (fun _ hz => hz.1)).prodMk continuous_snd.continuousOn
  have hcoordJ : _root_.Set.MapsTo (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2))
      (K ×ˢ _root_.Set.Icc a c) (J ×ˢ _root_.Set.Icc a c) := fun _ hz => ⟨hKJ hz.1, hz.2⟩
  filter_upwards [eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ (c := c) ha hbase]
    with k hk
  exact (hw.mul (hk.comp hcoord hcoordJ)).integrableOn_compact (hK.prod _root_.CompactIccSpace.isCompact_Icc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integrableOn_poleEndpoint_redLength_chart

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
