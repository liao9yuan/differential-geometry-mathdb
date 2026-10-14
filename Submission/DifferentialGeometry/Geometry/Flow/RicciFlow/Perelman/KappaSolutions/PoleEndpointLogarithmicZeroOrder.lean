import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityScalarIntegral
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthIntegralConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure
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

theorem integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {a c A : ℝ}
    (ha : 1 ≤ a)
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
    (c₀ : ℝ) (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a c)) :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    let Fk := fun k (z : E × ℝ) =>
      chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1) * w z *
        (c₀ - redLength ((U).term (phi (co.φ (rho k)))).S 0 p
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2)
    let F₀ := fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1) * w z *
        (c₀ - ell ((extChartAt I x).symm z.1, z.2))
    (∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (Fk k) (K ×ˢ _root_.Set.Icc a c) ν) ∧
      _root_.MeasureTheory.IntegrableOn F₀ (K ×ˢ _root_.Set.Icc a c) ν ∧
      _root_.Filter.Tendsto (fun k => ∫ z in K ×ˢ _root_.Set.Icc a c, Fk k z ∂ν) _root_.Filter.atTop
        (𝓝 (∫ z in K ×ˢ _root_.Set.Icc a c, F₀ z ∂ν)) := by
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ _root_.Set.Icc a c
  let f : ℕ → E × ℝ → ℝ := fun k z =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  let r : ℕ → E × ℝ → ℝ := fun k z =>
    chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let r₀ : E × ℝ → ℝ := fun z =>
    chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let G := fun k z => r k z * w z * (c₀ - f k z)
  let G₀ := fun z => r₀ z * w z * (c₀ - f₀ z)
  change (∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (G k) C ν) ∧
    _root_.MeasureTheory.IntegrableOn G₀ C ν ∧
      _root_.Filter.Tendsto (fun k => ∫ z in C, G k z ∂ν) _root_.Filter.atTop (𝓝 (∫ z in C, G₀ z ∂ν))
  have hC : IsCompact C := hK.prod _root_.CompactIccSpace.isCompact_Icc
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hcoord : ContinuousOn
      (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2)) C :=
    (((continuousOn_extChartAt_symm x).mono hKt).comp continuous_fst.continuousOn
      (fun _ hz => hz.1)).prodMk continuous_snd.continuousOn
  have hcoordJ : _root_.Set.MapsTo (fun z : E × ℝ => ((extChartAt I x).symm z.1, z.2))
      C (J ×ˢ _root_.Set.Icc a c) := fun _ hz => ⟨hKJ hz.1, hz.2⟩
  have hf : ∀ᶠ k in _root_.Filter.atTop, ContinuousOn (f k) C := by
    filter_upwards [hrho.eventually
      (eventually_continuousOn_poleEndpoint_redLength_on_compact_time_interval
        F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
        (c := c) ha0 hbase)] with k hk
    simpa only [f, Function.comp_def] using hk.comp hcoord hcoordJ
  have hr (k : ℕ) : ContinuousOn (r k) C :=
    continuousOn_poleEndpoint_chartDensity F hcar hreg b hbmem tau q hsigma
      Phi R bf hsrc htgt (co.φ (rho k)) ha x hKt
  have hr₀ : ContinuousOn r₀ C :=
    continuousOn_poleEndpoint_chartDensity_limit F hcar hreg b hbmem tau q hsigma
      Phi R co ha x hK hKt
  have hru : TendstoUniformlyOn r r₀ _root_.Filter.atTop C :=
    tendstoUniformlyOn_poleEndpoint_chartDensity F hcar hreg b hbmem tau q hsigma
      Phi R co ha rho hrho x hK hKt
  have hsource : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (G k) C ν := by
    filter_upwards [hf] with k hk
    exact ((hr k).mul hw |>.mul (continuousOn_const.sub hk)).integrableOn_compact hC
  obtain ⟨V, _hV, hupper⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha0 hbase
  let M := _root_.Max.max V 0
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
      (lCost_nonneg_of_scalar_nonneg _ 0 (ha0.trans_le hz.2.1).le hscalar _ _)
      (by positivity)
  let bound : E × ℝ → ℝ := fun z =>
    (‖r₀ z‖ + 1) * ‖w z‖ * (‖c₀‖ + M)
  have hbound : ∀ᶠ k in _root_.Filter.atTop, ∀ᵐ z ∂ν.restrict C, ‖G k z‖ ≤ bound z := by
    filter_upwards [hrho.eventually hupper,
      Metric.tendstoUniformlyOn_iff.mp hru 1 zero_lt_one] with k hk hkr
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    have hrf : ‖r k z - r₀ z‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using hkr z hz
    have hrbound : ‖r k z‖ ≤ ‖r₀ z‖ + 1 := by
      have ht := norm_add_le (r k z - r₀ z) (r₀ z)
      rw [sub_add_cancel] at ht
      linarith
    have hfbound : ‖f k z‖ ≤ M := by
      rw [Real.norm_of_nonneg (hnonneg k z hz)]
      exact (hk _ (hKJ hz.1) _ hz.2).trans (le_max_left _ _)
    have hsub : ‖c₀ - f k z‖ ≤ ‖c₀‖ + M :=
      (norm_sub_le _ _).trans (add_le_add le_rfl hfbound)
    dsimp only [G, bound]
    rw [norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hrbound (norm_nonneg _)) hsub
      (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))
  have hboundInt : _root_.MeasureTheory.Integrable bound (ν.restrict C) :=
    (((hr₀.norm.add continuousOn_const).mul hw.norm).mul
      continuousOn_const).integrableOn_compact hC
  have hlimit : ∀ᵐ z ∂ν.restrict C,
      Tendsto (fun k => G k z) _root_.Filter.atTop (𝓝 (G₀ z)) := by
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem hC.measurableSet] with z hz
    exact ((hru.tendsto_at hz).mul tendsto_const_nhds).mul
      (tendsto_const_nhds.sub (hconv _ (hKJ hz.1) _ hz.2))
  have hmeas : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.AEStronglyMeasurable (G k) (ν.restrict C) :=
    hsource.mono fun _ hk => hk.aestronglyMeasurable
  exact ⟨hsource, integrable_of_dominated_convergence bound hmeas hbound hboundInt hlimit,
    _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound hmeas hbound hboundInt hlimit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
