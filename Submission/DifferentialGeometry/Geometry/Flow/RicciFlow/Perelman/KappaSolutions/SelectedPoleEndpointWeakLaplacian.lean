import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientPoleEndpointWeakLaplacian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLaplacianIntegrability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
open scoped _root_.ContDiff _root_.Submission.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
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

namespace HalfLineMetricConvergenceData

theorem eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (hb : b < 0) {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (kappaSeq : ℕ → ℝ) (hseq : ∀ i, IsAncientKappaSolution (kappaSeq i) ((U).term i))
    (p0 : F.M) (a : P.M) {K : Set P.M} (hK : IsCompact K)
    (hchart : K ⊆ (chartAt H a).source) {δ T A0 : ℝ} (hδ : 1 < δ)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p0 (q (phi (co.φ k))) 1 ≤ A0)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W)
    (hWK : W ⊆ (extChartAt I a) '' K)
    {S : Set ℝ} (hS : IsOpen S) (hST : S ⊆ _root_.Set.Icc δ T)
    {μ : _root_.MeasureTheory.Measure E} [Measure.IsAddHaarMeasure μ] :
    ∀ᶠ k in _root_.Filter.atTop,
      let metric : ℝ → SmoothRiemannianMetric I P.M :=
        fun s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s)
      let ell : ℝ → P.M → ℝ := fun s y =>
        redLength ((U).term (phi (co.φ (rho k)))).S 0 p0 (Phi.map (co.φ (rho k)) y) s
      let f : ℝ × E → ℝ := fun p => scalarOnE (I := I) a (ell p.1) p.2
      let B : ℝ × E → ℝ := fun p => chartDensityOnE (metric p.1) a p.2 *
        ((1 / 2 : ℝ) * normGradSqFun (metric p.1) (ell p.1) ((extChartAt I a).symm p.2) -
          (1 / 2 : ℝ) * ((U).term (phi (co.φ (rho k)))).S.scalar (-p.1)
            (Phi.map (co.φ (rho k)) ((extChartAt I a).symm p.2)) +
          ((Module.finrank ℝ E : ℝ) - f p) / (2 * p.1))
      LocallyLipschitzOn (S ×ˢ W) f ∧
      _root_.MeasureTheory.LocallyIntegrableOn B (S ×ˢ W) (volume.prod μ) ∧
      (∀ i j : Fin (Module.finrank ℝ E),
        _root_.MeasureTheory.LocallyIntegrableOn
          (fun p : ℝ × E => chartDensityOnE (metric p.1) a p.2 *
            chartInvGramOnE (metric p.1) a i j p.2 *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E i))
          (S ×ˢ W) (volume.prod μ)) ∧
      ∀ q0 : ℝ × E, q0 ∈ S ×ˢ W →
      ∃ (J' : Set ℝ) (r : ℝ), IsOpen J' ∧ q0.1 ∈ J' ∧ J' ⊆ S ∧
        0 < r ∧ Metric.ball q0.2 r ⊆ W ∧
        ∀ φ : ℝ × E → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        tsupport φ ⊆ J' ×ˢ Metric.ball q0.2 r → (∀ p, 0 ≤ φ p) →
        0 ≤ ∫ p, B p * φ p +
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (metric p.1) a p.2 *
              chartInvGramOnE (metric p.1) a ij.1 ij.2 p.2) *
              fderiv ℝ (fun z => f (p.1, z)) p.2 (chartModelBasis E ij.1) *
              fderiv ℝ φ p (0, chartModelBasis E ij.2) ∂volume.prod μ := by
  have hWt : W ⊆ (extChartAt I a).target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWK hz
    exact (extChartAt I a).map_source (by simpa only [extChartAt_source] using hchart hy)
  have hWInv : _root_.Set.MapsTo (extChartAt I a).symm W K := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWK hz
    rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hchart hy)]
    exact hy
  have hSpos : S ⊆ _root_.Set.Ioi 1 := fun s hs => lt_of_lt_of_le hδ (hST hs).1
  have hraw : _root_.Filter.Tendsto (fun k => co.φ (rho k)) _root_.Filter.atTop atTop :=
    co.strictMono.tendsto_atTop.comp hrho
  obtain ⟨A, hregular⟩ :=
    exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappaSeq hseq p0 a hK hchart hδ hbase rho hrho hWconv hWK hST
  have hlocal :=
    eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg_of_ancient
      F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hb hF hK (μ := μ)
  have hintegrable := eventually_locallyIntegrableOn_poleEndpoint_redLength_chart_laplacian_rhs
    F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a hK (μ := μ)
  filter_upwards [hregular, hraw.eventually hlocal, hraw.eventually hintegrable]
    with k hkregular hklocal hkB
  intro metric ell f B
  have hlip : LocallyLipschitzOn (S ×ˢ W) f := by
    simpa only [f, ell, scalarOnE_def] using hkregular.1
  have hconc : ∀ s ∈ S, ConcaveOn ℝ W (fun z => f (s, z) - A z z / 2) := by
    simpa only [f, ell, scalarOnE_def] using hkregular.2
  have hB : _root_.MeasureTheory.LocallyIntegrableOn B (S ×ˢ W) (volume.prod μ) :=
    hkB S W hS hW hSpos hWt hWInv hlip
  refine ⟨hlip, hB, ?_, ?_⟩
  · intro i j
    exact locallyIntegrableOn_poleEndpoint_redLength_chart_laplacian_flux
      F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt p0 a (co.φ (rho k))
      hS hW (fun s hs => mem_Ici.mpr (le_of_lt (mem_Ioi.mp (hSpos hs)))) hWt hlip i j
  · exact hklocal S W hS hW hSpos hWt hWInv hlip A hconc hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_exists_nhds_integral_poleEndpoint_redLength_chart_laplacian_nonneg

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
