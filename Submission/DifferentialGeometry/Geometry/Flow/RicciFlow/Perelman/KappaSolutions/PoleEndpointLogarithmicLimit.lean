import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLogarithmicResidualConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientResidual
import Submission.DifferentialGeometry.Topology.Compactness.ProductInterval

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
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
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

private local instance cotangentDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.cotangentDualNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.cotangentDualNormedAddCommGroup target :: scope.openDecls } }

private local instance cotangentDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.cotangentDualNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.cotangentDualNormedSpace target :: scope.openDecls } }

private local instance cotangentBilinearNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.cotangentBilinearNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.cotangentBilinearNormedAddCommGroup target :: scope.openDecls } }

private local instance cotangentBilinearNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.cotangentBilinearNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.cotangentBilinearNormedSpace target :: scope.openDecls } }

private local instance spacetimeCotangentNormedAddCommGroup :
    NormedAddCommGroup ((E × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.spacetimeCotangentNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.spacetimeCotangentNormedAddCommGroup target :: scope.openDecls } }

private local instance spacetimeCotangentNormedSpace : NormedSpace ℝ ((E × ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.spacetimeCotangentNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.spacetimeCotangentNormedSpace target :: scope.openDecls } }

namespace HalfLineMetricConvergenceData

theorem integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities
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
    (x : P.M) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (extChartAt I x).target)
    (hWJ : _root_.Set.MapsTo (extChartAt I x).symm W J)
    (test : ℝ × E → ℝ) (htest : ContDiff ℝ 2 test)
    (htestc : HasCompactSupport test) (hsupport : tsupport test ⊆ _root_.Set.Ioo a c ×ˢ W)
    (hsource :
      let μ := modelHaar (E := E)
      let g := fun k s => gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - s)
      let l := fun k y s => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) s
      let r := fun k (z : ℝ × E) =>
        -(1 / 2 : ℝ) * ((U).term (phi (co.φ (rho k)))).S.scalar (-z.1)
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.2)) +
          ((Module.finrank ℝ E : ℝ) - l k ((extChartAt I x).symm z.2) z.1) / (2 * z.1)
      ∀ᶠ k in _root_.Filter.atTop, 0 ≤ ∫ z : ℝ × E,
        chartDensityOnE (g k z.1) x z.2 *
            ((1 / 2 : ℝ) * normGradSqFun (g k z.1) (fun y => l k y z.1)
              ((extChartAt I x).symm z.2) + r k z) * test z +
          (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (chartDensityOnE (g k z.1) x z.2 *
              chartInvGramOnE (g k z.1) x ij.1 ij.2 z.2) *
              fderiv ℝ (scalarOnE (I := I) x (fun y => l k y z.1)) z.2
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E ij.1) *
              fderiv ℝ test z (0, DifferentialGeometry.Tensor.Coordinates.chartModelBasis E ij.2))
                ∂volume.prod μ) :
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
    let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
    let density := fun z => chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
    let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
    let Q := fun z => density z *
      (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
        ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * test z +
          B z (d z) (fderiv ℝ (fun y => test (z.1, y)) z.2))
    Integrable Q ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E))) ∧
      0 ≤ ∫ z, Q z ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ).prod (modelHaar (E := E)) := by
  obtain ⟨a', c', K, haa, hcc, hK, hKW, hsupp⟩ :=
    htestc.exists_subset_closed_interval_prod hsupport
  let w : E × ℝ → ℝ := fun z => test z.swap
  let v : E × ℝ → E →L[ℝ] ℝ := fun z =>
    (fderiv ℝ w z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hwSmooth : ContDiff ℝ 2 w := htest.comp (contDiff_snd.prodMk contDiff_fst)
  have hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a' c') := hwSmooth.continuous.continuousOn
  have hv : ContinuousOn v (K ×ˢ _root_.Set.Icc a' c') :=
    ((hwSmooth.continuous_fderiv (by norm_num)).clm_comp continuous_const).continuousOn
  have hlim := integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc w hw v hv
  have hsourceEq := eventually_integral_poleEndpoint_redLength_chart_laplacian_eq_gradient
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
    rho hrho x hW hK hKW hWt hWJ haa hcc
  have htarget := integrable_poleEndpoint_logarithmic_residual_iff_and_integral_eq_joint
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
    rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc test
      (htest.differentiable (by norm_num)) hsupp
  have hselected := hlim (by
    filter_upwards [hsource, hsourceEq] with k hk heq
    rw [heq test (htest.differentiable (by norm_num)) hsupp] at hk
    simpa only [w, v, chartDensityOnE, sub_eq_add_neg, neg_mul, add_assoc,
      Prod.fst_swap, Prod.snd_swap] using hk)
  refine ⟨htarget.1.mpr hselected.1, ?_⟩
  rw [htarget.2]
  exact hselected.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_integral_poleEndpoint_logarithmic_nonneg_of_source_inequalities

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
