import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.GradientResidual
import Submission.DifferentialGeometry.Analysis.Integration.Integral.SpatialResidual
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointDifferentiabilityTail

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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.Topology

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

theorem eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p0 : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p0
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (x : P.M) {W K : Set E} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c) :
    let μ := modelHaar (E := E)
    let g := fun k s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s)
    let l := fun k y s => redLength ((U).term (phi (co.φ (rho k)))).S 0 p0
      (Phi.map (co.φ (rho k)) y) s
    let d := fun k (z : E × ℝ) =>
      (fderiv ℝ (fun v : E × ℝ => l k ((extChartAt I x).symm v.1) v.2) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let r := fun k (p : ℝ × E) =>
      -(1 / 2 : ℝ) *
        DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar
          ((U).term (phi (co.φ (rho k)))).S (-p.1)
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm p.2)) +
        ((Module.finrank ℝ E : ℝ) - l k ((extChartAt I x).symm p.2) p.1) / (2 * p.1)
    ∀ᶠ k in _root_.Filter.atTop, ∀ test : ℝ × E → ℝ,
      Differentiable ℝ test → tsupport test ⊆ _root_.Set.Icc a' c' ×ˢ K →
      (∫ p : ℝ × E,
        chartDensityOnE (g k p.1) x p.2 *
            ((1 / 2 : ℝ) * normGradSqFun (g k p.1) (fun y => l k y p.1)
              ((extChartAt I x).symm p.2) + r k p) * test p +
          (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (g k p.1) x p.2 *
              chartInvGramOnE (g k p.1) x ij.1 ij.2 p.2) *
              fderiv ℝ (scalarOnE (I := I) x (fun y => l k y p.1)) p.2
                (chartModelBasis E ij.1) *
              fderiv ℝ test p (0, chartModelBasis E ij.2)) ∂volume.prod μ) =
        ∫ z in K ×ˢ _root_.Set.Icc a' c',
          chartDensityOnE (g k z.2) x z.1 *
            (((1 / 2 : ℝ) *
                chartGradientBilin (g k z.2) x ((extChartAt I x).symm z.1)
                  (d k z) (d k z) + r k z.swap) * test z.swap +
              chartGradientBilin (g k z.2) x ((extChartAt I x).symm z.1)
                (d k z) ((fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
                  (ContinuousLinearMap.inl ℝ E ℝ))) ∂μ.prod volume := by
  dsimp only
  have hdiff := eventually_ae_differentiableAt_poleEndpoint_redLength_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p0 hJ
      (c := c) ha hbase x hW hWt hWJ
  filter_upwards [hrho.eventually hdiff] with k hk
  intro test htest hsupp
  apply integral_chart_laplacian_residual_eq_setIntegral_gradient
    (modelHaar (E := E))
    (fun s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s))
    x (fun y s => redLength ((U).term (phi (co.φ (rho k)))).S 0 p0
      (Phi.map (co.φ (rho k)) y) s)
    test (1 / 2)
    (fun p : ℝ × E => -(1 / 2 : ℝ) *
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar
        ((U).term (phi (co.φ (rho k)))).S (-p.1)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm p.2)) +
      ((Module.finrank ℝ E : ℝ) - redLength ((U).term (phi (co.φ (rho k)))).S 0 p0
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm p.2)) p.1) / (2 * p.1))
    hK.measurableSet measurableSet_Icc (hKW.trans hWt) htest hsupp
  filter_upwards [hk] with z hz hmem
  exact hz ⟨hKW hmem.1, lt_of_lt_of_le haa hmem.2.1,
    lt_of_le_of_lt hmem.2.2 hcc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient

theorem integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p0 : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 ≤ a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p0
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p0
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {W K : Set E} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    {a' c' : ℝ} (haa : a < a') (hcc : c' < c)
    (test : ℝ × E → ℝ) (htest : Differentiable ℝ test)
    (hsupport : tsupport test ⊆ _root_.Set.Icc a' c' ×ˢ K) :
    let μ := modelHaar (E := E)
    let f := fun p : ℝ × E => ell ((extChartAt I x).symm p.2, p.1)
    let ds := fun p : ℝ × E => fderiv ℝ (fun y : E => f (p.1, y)) p.2
    let es := fun p : ℝ × E => fderiv ℝ (fun y : E => test (p.1, y)) p.2
    let B := fun p : ℝ × E =>
      chartGradientBilin (co.gInf (1 - p.1)) x ((extChartAt I x).symm p.2)
    let density := fun p : ℝ × E =>
      chartDensity (co.gInf (1 - p.1)) x ((extChartAt I x).symm p.2)
    let scalar := fun p : ℝ × E =>
      metricScalarAt (co.gInf (1 - p.1)) ((extChartAt I x).symm p.2)
    let d := fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let e := fun z : E × ℝ =>
      (fderiv ℝ (fun v : E × ℝ => test v.swap) z).comp
        (ContinuousLinearMap.inl ℝ E ℝ)
    let S := fun p => density p *
      (((1 / 2 : ℝ) * B p (ds p) (ds p) - (1 / 2 : ℝ) * scalar p +
        ((Module.finrank ℝ E : ℝ) - f p) / (2 * p.1)) * test p + B p (ds p) (es p))
    let Q := fun z => density z.swap *
      (((1 / 2 : ℝ) * B z.swap (d z) (d z) - (1 / 2 : ℝ) * scalar z.swap +
        ((Module.finrank ℝ E : ℝ) - f z.swap) / (2 * z.2)) * test z.swap +
          B z.swap (d z) (e z))
    (_root_.MeasureTheory.Integrable S (volume.prod μ) ↔ _root_.MeasureTheory.IntegrableOn Q (K ×ˢ _root_.Set.Icc a' c') (μ.prod _root_.MeasureTheory.MeasureSpace.volume)) ∧
      (∫ p, S p ∂volume.prod μ) = ∫ z in K ×ˢ _root_.Set.Icc a' c', Q z ∂μ.prod volume := by
  have hdiff := ae_differentiableAt_poleEndpoint_redLength_limit_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p0 hJ
      ha hbase rho hrho ell hconv x hW hWt hWJ
  have hsmall : ∀ᵐ z ∂(modelHaar (E := E)).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ),
      z ∈ K ×ˢ _root_.Set.Icc a' c' → DifferentiableAt ℝ
        (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2)) z := by
    filter_upwards [hdiff] with z hz hmem
    exact hz ⟨hKW hmem.1, lt_of_lt_of_le haa hmem.2.1,
      lt_of_le_of_lt hmem.2.2 hcc⟩
  have h := Analysis.integrable_spatial_residual_iff_and_integral_eq_joint
    (modelHaar (E := E))
    (fun v : E × ℝ => ell ((extChartAt I x).symm v.1, v.2))
    test (1 / 2)
    (fun p : ℝ × E => chartDensity (co.gInf (1 - p.1)) x ((extChartAt I x).symm p.2))
    (fun p : ℝ × E => -(1 / 2 : ℝ) *
      metricScalarAt (co.gInf (1 - p.1)) ((extChartAt I x).symm p.2) +
      ((Module.finrank ℝ E : ℝ) - ell ((extChartAt I x).symm p.2, p.1)) / (2 * p.1))
    (fun p : ℝ × E =>
      chartGradientBilin (co.gInf (1 - p.1)) x ((extChartAt I x).symm p.2))
    hK.measurableSet measurableSet_Icc htest hsupport hsmall
  simpa only [sub_eq_add_neg, neg_mul, add_assoc, Prod.fst_swap, Prod.snd_swap] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
