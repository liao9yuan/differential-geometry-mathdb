import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointScalarConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointScalarContinuity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

private theorem poleEndpoint_scalar_chart_tendstoUniformlyOn
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target) :
    TendstoUniformlyOn
      (fun k (z : E × ℝ) => ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)))
      (fun z => metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1))
      atTop (K ×ˢ _root_.Set.Icc a c) := by
  let J : Set P.M := (extChartAt I x).symm '' K
  have hJ : IsCompact J :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hKt)
  have hu := tendstoUniformlyOn_poleEndpoint_scalar
    F hcar hreg b hbmem tau q hsigma Phi R co (c := c) ha hJ
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro epsilon hepsilon
  filter_upwards [hrho.eventually (hu epsilon hepsilon)] with k hk
  intro z hz
  exact hk (z.2, (extChartAt I x).symm z.1) ⟨hz.2, _root_.Set.mem_image_of_mem _ hz.1⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_scalar_chart_tendstoUniformlyOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_scalar_chart_tendstoUniformlyOn target :: scope.openDecls } }

private theorem poleEndpoint_scalar_limit_chart_continuousOn
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target) :
    ContinuousOn
      (fun z : E × ℝ => metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1))
      (K ×ˢ _root_.Set.Icc a c) := by
  have hcontinuous := PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart
    F hcar hreg b hbmem tau q hsigma Phi co.φ co.strictMono.tendsto_atTop x hK hKt (c := c) ha
  have hu := poleEndpoint_scalar_chart_tendstoUniformlyOn
    F hcar hreg b hbmem tau q hsigma Phi R co (c := c) ha id _root_.Filter.tendsto_id x hK hKt
  exact hu.continuousOn hcontinuous.frequently

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_scalar_limit_chart_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_scalar_limit_chart_continuousOn target :: scope.openDecls } }

theorem integrableOn_poleEndpoint_scalar_limit_chart
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    _root_.MeasureTheory.IntegrableOn
      (fun z : E × ℝ => w z *
        metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1))
      (K ×ˢ _root_.Set.Icc a c)
      ((DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) := by
  have hcont := poleEndpoint_scalar_limit_chart_continuousOn
    F hcar hreg b hbmem tau q hsigma Phi R co (c := c) ha x hK hKt
  exact (hw.mul hcont).integrableOn_compact (hK.prod _root_.CompactIccSpace.isCompact_Icc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_scalar_limit_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_scalar_limit_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_scalar_limit_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrableOn_poleEndpoint_scalar_limit_chart

theorem tendsto_integral_poleEndpoint_scalar_chart
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I x).target)
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    _root_.Filter.Tendsto (fun k => ∫ z in K ×ˢ _root_.Set.Icc a c, w z *
      ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in K ×ˢ _root_.Set.Icc a c, w z *
        metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1) ∂ν)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ _root_.Set.Icc a c
  let f : ℕ → E × ℝ → ℝ := fun k z =>
    ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
  let f₀ : E × ℝ → ℝ := fun z =>
    metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
  have hC : IsCompact C := hK.prod _root_.CompactIccSpace.isCompact_Icc
  have hu : TendstoUniformlyOn f f₀ _root_.Filter.atTop C :=
    poleEndpoint_scalar_chart_tendstoUniformlyOn
      F hcar hreg b hbmem tau q hsigma Phi R co ha rho hrho x hK hKt
  have hcontinuous : ∀ᶠ k in _root_.Filter.atTop, ContinuousOn (f k) C := by
    simpa only [Function.comp_apply] using
      PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart
        F hcar hreg b hbmem tau q hsigma Phi (co.φ ∘ rho)
        (co.strictMono.tendsto_atTop.comp hrho) x hK hKt (c := c) ha
  have hlimCont : ContinuousOn f₀ C := hu.continuousOn hcontinuous.frequently
  have hsourceInt : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.Integrable (fun z => w z * f k z) (ν.restrict C) :=
    hcontinuous.mono fun _ hk => (hw.mul hk).integrableOn_compact hC
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hlimCont
  have hbound : ∀ᶠ k in _root_.Filter.atTop, ∀ᵐ z ∂ν.restrict C,
      ‖w z * f k z‖ ≤ ‖w z‖ * (B + 1) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one] with k hk
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    have hclose : ‖f k z - f₀ z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hk z hz
    have htriangle : ‖f k z‖ ≤ ‖f k z - f₀ z‖ + ‖f₀ z‖ := by
      calc
        ‖f k z‖ = ‖(f k z - f₀ z) + f₀ z‖ := by rw [sub_add_cancel]
        _ ≤ ‖f k z - f₀ z‖ + ‖f₀ z‖ := norm_add_le _ _
    have hfbound : ‖f k z‖ ≤ B + 1 := by linarith [hB z hz]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hfbound (norm_nonneg _)
  have hintegrable : _root_.MeasureTheory.Integrable (fun z => ‖w z‖ * (B + 1)) (ν.restrict C) :=
    (hw.norm.mul continuousOn_const).integrableOn_compact hC
  have hlimit : ∀ᵐ z ∂ν.restrict C,
      Tendsto (fun k => w z * f k z) _root_.Filter.atTop (𝓝 (w z * f₀ z)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    exact tendsto_const_nhds.mul (hu.tendsto_at hz)
  exact _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖w z‖ * (B + 1))
    (hsourceInt.mono fun _ hk => hk.aestronglyMeasurable) hbound hintegrable hlimit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_scalar_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_scalar_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_scalar_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_scalar_chart

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
