import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthEquicontinuity
import Submission.DifferentialGeometry.Geometry.Metric.ChartLipschitz.Joint
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

theorem ae_eventually_differentiableAt_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod _root_.MeasureTheory.MeasureSpace.volume,
      z ∈ W ×ˢ _root_.Set.Ioo a c → ∀ᶠ k in _root_.Filter.atTop,
        DifferentiableAt ℝ (fun v : E × ℝ =>
          redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z := by
  obtain ⟨C, Dt, hC, hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmodulus
  have hdiff (k : ℕ) :
      ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod _root_.MeasureTheory.MeasureSpace.volume,
        N ≤ k → z ∈ W ×ˢ _root_.Set.Ioo a c →
          DifferentiableAt ℝ (fun v : E × ℝ =>
            redLength ((U).term (phi (co.φ k))).S 0 p
              (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) z := by
    by_cases hk : N ≤ k
    · have hlip : LocallyLipschitzOn (W ×ˢ _root_.Set.Ioo a c)
          (fun v : E × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) ((extChartAt I x).symm v.1)) v.2) := by
        apply Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound
          R x hWt hWJ (J := _root_.Set.Ioo a c)
          (f := fun z : P.M × ℝ => redLength ((U).term (phi (co.φ k))).S 0 p
            (Phi.map (co.φ k) z.1) z.2) hC hDt zero_lt_one
        intro y hy w hw s hs t ht hdist
        simpa only [Real.dist_eq] using hN k hk y hy w hw s ⟨hs.1.le, hs.2.le⟩
          t ⟨ht.1.le, ht.2.le⟩ hdist
      filter_upwards [hlip.ae_differentiableAt_of_isOpen (hW.prod isOpen_Ioo)] with z hz
      exact fun _ hzw => hz hzw
    · exact Filter.Eventually.of_forall fun _ h _ => False.elim (hk h)
  filter_upwards [ae_all_iff.mpr hdiff] with z hz
  intro hzw
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with k hk
  exact hz k hk hzw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_differentiableAt_poleEndpoint_redLength_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_differentiableAt_poleEndpoint_redLength_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_differentiableAt_poleEndpoint_redLength_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_eventually_differentiableAt_poleEndpoint_redLength_chart

theorem ae_differentiableAt_poleEndpoint_redLength_limit_chart
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
    (x : P.M) {W : Set E} (hW : IsOpen W) (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J) :
    ∀ᵐ z ∂(DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod _root_.MeasureTheory.MeasureSpace.volume,
      z ∈ W ×ˢ _root_.Set.Ioo a c →
        DifferentiableAt ℝ
          (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z := by
  obtain ⟨C, Dt, hC, hDt, hmodulus⟩ :=
    exists_eventually_abs_poleEndpoint_redLength_sub_le_distance_add_time_on_compact
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ
      (c := c) ha hbase
  have hlim : ∀ y ∈ J, ∀ w ∈ J, ∀ s ∈ _root_.Set.Icc a c, ∀ t ∈ _root_.Set.Icc a c,
      riemannianEDistOf R y w < ENNReal.ofReal 1 →
      |ell (y, s) - ell (w, t)| ≤
        C * (riemannianEDistOf R y w).toReal + Dt * |s - t| := by
    intro y hy w hw s hs t ht hdist
    apply le_of_tendsto ((hconv y hy s hs).sub (hconv w hw t ht)).abs
    filter_upwards [hrho.eventually hmodulus] with k hk
    exact hk y hy w hw s hs t ht hdist
  have hlip : LocallyLipschitzOn (W ×ˢ _root_.Set.Ioo a c)
      (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) := by
    apply Geometry.Riemannian.locallyLipschitzOn_chart_prod_of_edist_bound
      R x hWt hWJ hC hDt zero_lt_one
    intro y hy w hw s hs t ht hdist
    simpa only [Real.dist_eq] using hlim y hy w hw s ⟨hs.1.le, hs.2.le⟩
      t ⟨ht.1.le, ht.2.le⟩ hdist
  exact hlip.ae_differentiableAt_of_isOpen (hW.prod isOpen_Ioo)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.ae_differentiableAt_poleEndpoint_redLength_limit_chart

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
