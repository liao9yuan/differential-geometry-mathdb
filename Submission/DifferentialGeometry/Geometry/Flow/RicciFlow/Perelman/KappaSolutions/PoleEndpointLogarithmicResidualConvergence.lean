import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientBilinearConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointLogarithmicZeroOrder

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

namespace HalfLineMetricConvergenceData

theorem integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual
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
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a' c'))
    (v : E × ℝ → E →L[ℝ] ℝ) (hv : ContinuousOn v (K ×ˢ _root_.Set.Icc a' c')) :
    let ν := (modelHaar (E := E)).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    let f := fun k (z : E × ℝ) =>
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
    let f₀ := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
    let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let r := fun k (z : E × ℝ) =>
      chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let r₀ := fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let B := fun k (z : E × ℝ) =>
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let B₀ := fun z : E × ℝ =>
      chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let S := fun k (z : E × ℝ) =>
      ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
    let S₀ := fun z : E × ℝ =>
      metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
    let Q := fun k z => r k z *
      (((1 / 2 : ℝ) * B k z (d k z) (d k z) - (1 / 2 : ℝ) * S k z +
        ((Module.finrank ℝ E : ℝ) - f k z) / (2 * z.2)) * w z +
          B k z (d k z) (v z))
    let Q₀ := fun z => r₀ z *
      (((1 / 2 : ℝ) * B₀ z (d₀ z) (d₀ z) - (1 / 2 : ℝ) * S₀ z +
        ((Module.finrank ℝ E : ℝ) - f₀ z) / (2 * z.2)) * w z +
          B₀ z (d₀ z) (v z))
    (∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (Q k) (K ×ˢ _root_.Set.Icc a' c') ν) ∧
      _root_.MeasureTheory.IntegrableOn Q₀ (K ×ˢ _root_.Set.Icc a' c') ν ∧
      _root_.Filter.Tendsto (fun k => ∫ z in K ×ˢ _root_.Set.Icc a' c', Q k z ∂ν) _root_.Filter.atTop
        (𝓝 (∫ z in K ×ˢ _root_.Set.Icc a' c', Q₀ z ∂ν)) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let ν := (modelHaar (E := E)).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let C := K ×ˢ _root_.Set.Icc a' c'
  let f := fun k (z : E × ℝ) =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
  let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let r := fun k (z : E × ℝ) =>
    chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let r₀ := fun z : E × ℝ =>
    chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let B := fun k (z : E × ℝ) =>
    chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1)
  let B₀ := fun z : E × ℝ =>
    chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
  let S := fun k (z : E × ℝ) =>
    ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
  let S₀ := fun z : E × ℝ =>
    metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
  let e := fun k z => (w z * r k z) * B k z (d k z) (d k z)
  let e₀ := fun z => (w z * r₀ z) * B₀ z (d₀ z) (d₀ z)
  let s := fun k z => w z * r k z * S k z
  let s₀ := fun z => w z * r₀ z * S₀ z
  let z₀ := fun k z => r k z * (w z / (2 * z.2)) *
    ((Module.finrank ℝ E : ℝ) - f k z)
  let zInf := fun z => r₀ z * (w z / (2 * z.2)) *
    ((Module.finrank ℝ E : ℝ) - f₀ z)
  let l := fun k z => r k z * B k z (d k z) (v z)
  let l₀ := fun z => r₀ z * B₀ z (d₀ z) (v z)
  have he := integrable_and_tendsto_integral_poleEndpoint_redLength_gradient_bilinear
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc w hw v hv
  have hl := integrable_and_tendsto_integral_poleEndpoint_redLength_gradient_bilinear
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc
    (fun _ => 1) continuousOn_const v hv
  have ha' : 1 ≤ a' := (ha.trans haa).le
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hs := integrableOn_and_tendsto_integral_poleEndpoint_chartDensity_mul_scalar
    F hcar hreg b hbmem tau q hsigma Phi R co (c := c') ha' rho hrho x hK hKt w hw
  have htime : ContinuousOn (fun z : E × ℝ => w z / (2 * z.2)) C :=
    hw.div (continuousOn_const.mul continuous_snd.continuousOn) (fun z hz =>
      mul_ne_zero (by norm_num) (ne_of_gt (zero_lt_one.trans_le (ha'.trans hz.2.1))))
  have hz := integrable_and_tendsto_integral_poleEndpoint_chartDensity_mul_sub_redLength
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c') ha' hbase
    rho hrho ell
    (fun y hy t ht => hconv y hy t ⟨haa.le.trans ht.1, ht.2.trans hcc.le⟩)
    x hK hKt (fun y hy => hWJ (hKW hy)) (Module.finrank ℝ E : ℝ)
    (fun z => w z / (2 * z.2)) htime
  have heSrc : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (e k) C ν := by
    filter_upwards [he.1] with k hk
    simpa only [e, r, B, d, f, smul_apply, smul_eq_mul] using hk.2
  have heInf : _root_.MeasureTheory.IntegrableOn e₀ C ν := by
    simpa only [e₀, r₀, B₀, d₀, f₀, smul_apply, smul_eq_mul] using he.2.2.1
  have heConv : _root_.Filter.Tendsto (fun k => ∫ z in C, e k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, e₀ z ∂ν)) := by
    simpa only [e, e₀, r, r₀, B, B₀, d, d₀, f, f₀, smul_apply, smul_eq_mul] using he.2.2.2.2
  have hlSrc : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (l k) C ν := by
    filter_upwards [hl.1] with k hk
    simpa only [l, r, B, d, f, one_mul, smul_apply, smul_eq_mul] using hk.1
  have hlInf : _root_.MeasureTheory.IntegrableOn l₀ C ν := by
    simpa only [l₀, r₀, B₀, d₀, f₀, one_mul, smul_apply, smul_eq_mul] using hl.2.1
  have hlConv : _root_.Filter.Tendsto (fun k => ∫ z in C, l k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, l₀ z ∂ν)) := by
    simpa only [l, l₀, r, r₀, B, B₀, d, d₀, f, f₀, one_mul, smul_apply, smul_eq_mul]
      using hl.2.2.2.1
  have hsSrc : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (s k) C ν := hs.2.1
  have hsInf : _root_.MeasureTheory.IntegrableOn s₀ C ν := hs.1
  have hsConv : _root_.Filter.Tendsto (fun k => ∫ z in C, s k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, s₀ z ∂ν)) := hs.2.2
  have hzSrc : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (z₀ k) C ν := hz.1
  have hzInf : _root_.MeasureTheory.IntegrableOn zInf C ν := hz.2.1
  have hzConv : _root_.Filter.Tendsto (fun k => ∫ z in C, z₀ k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, zInf z ∂ν)) := hz.2.2
  let Q := fun k z => (1 / 2 : ℝ) * e k z - (1 / 2 : ℝ) * s k z + z₀ k z + l k z
  let Q₀ := fun z => (1 / 2 : ℝ) * e₀ z - (1 / 2 : ℝ) * s₀ z + zInf z + l₀ z
  have hQSrc : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (Q k) C ν := by
    filter_upwards [heSrc, hsSrc, hzSrc, hlSrc] with k hkE hkS hkZ hkL
    exact (((hkE.const_mul (1 / 2 : ℝ)).sub (hkS.const_mul (1 / 2 : ℝ))).add hkZ).add hkL
  have hQInf : _root_.MeasureTheory.IntegrableOn Q₀ C ν :=
    (((heInf.const_mul (1 / 2 : ℝ)).sub (hsInf.const_mul (1 / 2 : ℝ))).add hzInf).add hlInf
  have hQInt (k : ℕ) (hkE : _root_.MeasureTheory.IntegrableOn (e k) C ν) (hkS : _root_.MeasureTheory.IntegrableOn (s k) C ν)
      (hkZ : _root_.MeasureTheory.IntegrableOn (z₀ k) C ν) (hkL : _root_.MeasureTheory.IntegrableOn (l k) C ν) :
      (∫ z in C, Q k z ∂ν) =
        (1 / 2 : ℝ) * (∫ z in C, e k z ∂ν) - (1 / 2 : ℝ) * (∫ z in C, s k z ∂ν) +
          (∫ z in C, z₀ k z ∂ν) + ∫ z in C, l k z ∂ν := by
    dsimp only [Q]
    have hE := hkE.const_mul (1 / 2 : ℝ)
    have hS := hkS.const_mul (1 / 2 : ℝ)
    rw [_root_.MeasureTheory.integral_add
      (f := fun z => (1 / 2 : ℝ) * e k z - (1 / 2 : ℝ) * s k z + z₀ k z)
      (g := l k) ((hE.sub hS).add hkZ) hkL]
    rw [_root_.MeasureTheory.integral_add
      (f := fun z => (1 / 2 : ℝ) * e k z - (1 / 2 : ℝ) * s k z)
      (g := z₀ k) (hE.sub hS) hkZ]
    rw [_root_.MeasureTheory.integral_sub (f := fun z => (1 / 2 : ℝ) * e k z)
      (g := fun z => (1 / 2 : ℝ) * s k z) hE hS,
      _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  have hQInt₀ : (∫ z in C, Q₀ z ∂ν) =
      (1 / 2 : ℝ) * (∫ z in C, e₀ z ∂ν) - (1 / 2 : ℝ) * (∫ z in C, s₀ z ∂ν) +
        (∫ z in C, zInf z ∂ν) + ∫ z in C, l₀ z ∂ν := by
    dsimp only [Q₀]
    have hE := heInf.const_mul (1 / 2 : ℝ)
    have hS := hsInf.const_mul (1 / 2 : ℝ)
    rw [_root_.MeasureTheory.integral_add
      (f := fun z => (1 / 2 : ℝ) * e₀ z - (1 / 2 : ℝ) * s₀ z + zInf z)
      (g := l₀) ((hE.sub hS).add hzInf) hlInf]
    rw [_root_.MeasureTheory.integral_add
      (f := fun z => (1 / 2 : ℝ) * e₀ z - (1 / 2 : ℝ) * s₀ z)
      (g := zInf) (hE.sub hS) hzInf]
    rw [_root_.MeasureTheory.integral_sub (f := fun z => (1 / 2 : ℝ) * e₀ z)
      (g := fun z => (1 / 2 : ℝ) * s₀ z) hE hS,
      _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  have hQConv : _root_.Filter.Tendsto (fun k => ∫ z in C, Q k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, Q₀ z ∂ν)) := by
    rw [hQInt₀]
    apply ((((tendsto_const_nhds.mul heConv).sub
      (tendsto_const_nhds.mul hsConv)).add hzConv).add hlConv).congr'
    filter_upwards [heSrc, hsSrc, hzSrc, hlSrc] with k hkE hkS hkZ hkL
    exact (hQInt k hkE hkS hkZ hkL).symm
  have hQeq (k : ℕ) : Q k = fun z => r k z *
      (((1 / 2 : ℝ) * B k z (d k z) (d k z) - (1 / 2 : ℝ) * S k z +
        ((Module.finrank ℝ E : ℝ) - f k z) / (2 * z.2)) * w z +
          B k z (d k z) (v z)) := by
    funext z
    dsimp only [Q, e, s, z₀, l]
    simp only [div_eq_mul_inv]
    ring
  have hQeq₀ : Q₀ = fun z => r₀ z *
      (((1 / 2 : ℝ) * B₀ z (d₀ z) (d₀ z) - (1 / 2 : ℝ) * S₀ z +
        ((Module.finrank ℝ E : ℝ) - f₀ z) / (2 * z.2)) * w z +
          B₀ z (d₀ z) (v z)) := by
    funext z
    dsimp only [Q₀, e₀, s₀, zInf, l₀]
    simp only [div_eq_mul_inv]
    ring
  simpa only [hQeq, hQeq₀] using And.intro hQSrc (And.intro hQInf hQConv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual

theorem integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities
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
    (w : E × ℝ → ℝ) (hw : ContinuousOn w (K ×ˢ _root_.Set.Icc a' c'))
    (v : E × ℝ → E →L[ℝ] ℝ) (hv : ContinuousOn v (K ×ˢ _root_.Set.Icc a' c')) :
    let ν := (modelHaar (E := E)).prod (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    let f := fun k (z : E × ℝ) =>
      redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
    let f₀ := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
    let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    let r := fun k (z : E × ℝ) =>
      chartDensity (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let r₀ := fun z : E × ℝ =>
      chartDensity (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let B := fun k (z : E × ℝ) =>
      chartGradientBilin (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
        ((extChartAt I x).symm z.1)
    let B₀ := fun z : E × ℝ =>
      chartGradientBilin (co.gInf (1 - z.2)) x ((extChartAt I x).symm z.1)
    let S := fun k (z : E × ℝ) =>
      ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
        (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
    let S₀ := fun z : E × ℝ =>
      metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
    let Q := fun k z => r k z *
      (((1 / 2 : ℝ) * B k z (d k z) (d k z) - (1 / 2 : ℝ) * S k z +
        ((Module.finrank ℝ E : ℝ) - f k z) / (2 * z.2)) * w z +
          B k z (d k z) (v z))
    let Q₀ := fun z => r₀ z *
      (((1 / 2 : ℝ) * B₀ z (d₀ z) (d₀ z) - (1 / 2 : ℝ) * S₀ z +
        ((Module.finrank ℝ E : ℝ) - f₀ z) / (2 * z.2)) * w z +
          B₀ z (d₀ z) (v z))
    (∀ᶠ k in _root_.Filter.atTop, 0 ≤ ∫ z in K ×ˢ _root_.Set.Icc a' c', Q k z ∂ν) →
      _root_.MeasureTheory.IntegrableOn Q₀ (K ×ˢ _root_.Set.Icc a' c') ν ∧
        0 ≤ ∫ z in K ×ˢ _root_.Set.Icc a' c', Q₀ z ∂ν := by
  dsimp only
  intro hsource
  have h := integrable_and_tendsto_integral_poleEndpoint_logarithmic_residual
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc w hw v hv
  exact ⟨h.2.1, ge_of_tendsto h.2.2 hsource⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_logarithmic_residual_nonneg_of_source_inequalities

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
