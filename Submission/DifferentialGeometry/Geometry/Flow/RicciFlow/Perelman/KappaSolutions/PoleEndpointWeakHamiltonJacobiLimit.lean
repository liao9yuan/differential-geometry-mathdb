import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientEnergy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointWeakHamiltonJacobi
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointReducedLengthIntegralConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointScalarIntegralConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGradientIntegrability

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

namespace HalfLineMetricConvergenceData

theorem poleEndpoint_redLength_limit_weak_hamilton_jacobi
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
    (ψ : E × ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψC : tsupport ψ ⊆ K ×ˢ _root_.Set.Icc a' c') :
    let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
      (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
    let f := fun z : E × ℝ => ell ((extChartAt I x).symm z.1, z.2)
    let d := fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ E ℝ)
    (∫ z in K ×ˢ _root_.Set.Icc a' c', f z * fderiv ℝ ψ z (0, 1) ∂ν) =
      (1 / 2 : ℝ) * (∫ z in K ×ˢ _root_.Set.Icc a' c', ψ z *
        chartGradientBilin (co.gInf (1 - z.2)) x
          ((extChartAt I x).symm z.1) (d z) (d z) ∂ν) -
      (1 / 2 : ℝ) * (∫ z in K ×ˢ _root_.Set.Icc a' c', ψ z *
        metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1) ∂ν) +
      ∫ z in K ×ˢ _root_.Set.Icc a' c', ψ z / (2 * z.2) * f z ∂ν := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := (hF 0).notFlat
    exact DifferentialGeometry.Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (((U).term 0).S.base.metric t) y (by norm_num : 0 < 4)
      (((U).term 0).S.base.rm04 t y) hy⟩
  let ν := (DifferentialGeometry.Integral.Measure.modelHaar (E := E)).prod
    (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)
  let C : Set (E × ℝ) := K ×ˢ _root_.Set.Icc a' c'
  let _ : _root_.MeasureTheory.IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr
    (hK.prod _root_.CompactIccSpace.isCompact_Icc).measure_ne_top
  let f : ℕ → E × ℝ → ℝ := fun k z =>
    redLength ((U).term (phi (co.φ (rho k)))).S 0 p
      (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) z.2
  let f₀ : E × ℝ → ℝ := fun z => ell ((extChartAt I x).symm z.1, z.2)
  let d := fun k z => (fderiv ℝ (f k) z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let d₀ := fun z => (fderiv ℝ f₀ z).comp (ContinuousLinearMap.inl ℝ E ℝ)
  let Q := fun k z => chartGradientBilin
    (gSeqExt Phi R bf hsrc htgt (co.φ (rho k)) (1 - z.2)) x
      ((extChartAt I x).symm z.1) (d k z) (d k z)
  let Q₀ := fun z => chartGradientBilin (co.gInf (1 - z.2)) x
    ((extChartAt I x).symm z.1) (d₀ z) (d₀ z)
  let S : ℕ → E × ℝ → ℝ := fun k z => ((U).term (phi (co.φ (rho k)))).S.scalar (-z.2)
    (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1))
  let S₀ : E × ℝ → ℝ := fun z => metricScalarAt (co.gInf (1 - z.2)) ((extChartAt I x).symm z.1)
  let dψ := fun z => fderiv ℝ ψ z (0, 1)
  let V := fun z => ψ z / (2 * z.2)
  have ha' : 1 ≤ a' := (ha.trans haa).le
  have ha'pos : 0 < a' := zero_lt_one.trans_le ha'
  have hinterval : _root_.Set.Icc a' c' ⊆ _root_.Set.Icc a c := fun _ ht =>
    ⟨haa.le.trans ht.1, ht.2.trans hcc.le⟩
  have hKt : K ⊆ (extChartAt I x).target := hKW.trans hWt
  have hKJ : _root_.Set.MapsTo (extChartAt I x).symm K J := hWJ.mono_left hKW
  have hconv' := fun y hy t ht => hconv y hy t (hinterval ht)
  have hψon : ContinuousOn ψ C := hψ.continuous.continuousOn
  have hdψ : ContinuousOn dψ C :=
    ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn
  have hV : ContinuousOn V C := hψon.div
    (continuousOn_const.mul continuous_snd.continuousOn) (by
      intro z hz
      exact mul_ne_zero (by norm_num) (ha'pos.trans_le hz.2.1).ne')
  have hlinear : _root_.Filter.Tendsto (fun k => ∫ z in C, dψ z * f k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, dψ z * f₀ z ∂ν)) :=
    tendsto_integral_poleEndpoint_redLength_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha'pos hbase
      rho hrho ell hconv' x hK hKt hKJ dψ hdψ
  have hzero : _root_.Filter.Tendsto (fun k => ∫ z in C, V z * f k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, V z * f₀ z ∂ν)) :=
    tendsto_integral_poleEndpoint_redLength_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha'pos hbase
      rho hrho ell hconv' x hK hKt hKJ V hV
  have hscalar : _root_.Filter.Tendsto (fun k => ∫ z in C, ψ z * S k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, ψ z * S₀ z ∂ν)) :=
    tendsto_integral_poleEndpoint_scalar_chart
      F hcar hreg b hbmem tau q hsigma Phi R co ha' rho hrho x hK hKt ψ hψon
  have henergy : _root_.Filter.Tendsto (fun k => ∫ z in C, ψ z * Q k z ∂ν) _root_.Filter.atTop
      (𝓝 (∫ z in C, ψ z * Q₀ z ∂ν)) := by
    have he := tendsto_integral_poleEndpoint_redLength_gradient_quadratic_unweighted
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p hJ ha hbase rho hrho ell hconv x hW hK hKW hWt hWJ haa hcc ψ hψon
    simpa only [smul_apply, smul_eq_mul] using he
  have hzeroInt : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (fun z => V z * f k z) C ν :=
    hrho.eventually (eventually_integrableOn_poleEndpoint_redLength_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha'pos hbase
      x hK hKt hKJ V hV)
  have hscalarInt : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (fun z => ψ z * S k z) C ν := by
    have hc := PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart
      F hcar hreg b hbmem tau q hsigma Phi (co.φ ∘ rho)
      (co.strictMono.tendsto_atTop.comp hrho) x hK hKt (c := c') ha'
    filter_upwards [hc] with k hk
    exact (hψon.mul hk).integrableOn_compact (hK.prod _root_.CompactIccSpace.isCompact_Icc)
  have henergyInt : ∀ᶠ k in _root_.Filter.atTop, _root_.MeasureTheory.IntegrableOn (fun z => ψ z * Q k z) C ν := by
    have hi := eventually_integrableOn_poleEndpoint_redLength_gradient_quadratic
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c') ha' hbase
      rho hrho x hW hK hKW hWt hWJ ν ψ hψon
    simpa only [smul_apply, smul_eq_mul] using hi
  have hψW : tsupport ψ ⊆ W ×ˢ _root_.Set.Ioo a c := by
    intro z hz
    obtain ⟨hzK, hzT⟩ := hψC hz
    exact ⟨hKW hzK, haa.trans_le hzT.1, hzT.2.trans_lt hcc⟩
  have hhj := hrho.eventually (eventually_poleEndpoint_redLength_weak_hamilton_jacobi
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ (c := c) ha.le hbase
    x hW hWt hWJ ψ hψ hψc hψW)
  have hid : ∀ᶠ k in _root_.Filter.atTop,
      (∫ z in C, dψ z * f k z ∂ν) =
        (1 / 2 : ℝ) * (∫ z in C, ψ z * Q k z ∂ν) -
        (1 / 2 : ℝ) * (∫ z in C, ψ z * S k z ∂ν) +
        ∫ z in C, V z * f k z ∂ν := by
    filter_upwards [hhj, henergyInt, hscalarInt, hzeroInt] with k hk hQi hSi hVi
    have hscalarEq (z : E × ℝ) :
        ((Y).term (phi (co.φ (rho k)))).S.scalar (1 - z.2)
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) = S k z := by
      change metricScalarAt (((Y).term (phi (co.φ (rho k)))).S.base.metric (1 - z.2))
          (Phi.map (co.φ (rho k)) ((extChartAt I x).symm z.1)) = _
      rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
      have ht : 1 - z.2 - 1 = -z.2 := by ring
      rw [ht]
      rfl
    have hleft : (∫ z in C, dψ z * f k z ∂ν) =
        ∫ z, f k z * fderiv ℝ ψ z (0, 1) ∂ν := by
      rw [_root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
      · apply _root_.MeasureTheory.integral_congr_ae
        exact Eventually.of_forall fun z => mul_comm _ _
      · have hn : z ∉ tsupport ψ := fun h => hz (hψC h)
        simp only [dψ, fderiv_of_notMem_tsupport ℝ hn, zero_apply, _root_.MulZeroClass.zero_mul]
    have hright :
        (∫ z, ((1 / 2 : ℝ) * Q k z - (1 / 2 : ℝ) * S k z +
          f k z / (2 * z.2)) * ψ z ∂ν) =
        (1 / 2 : ℝ) * (∫ z in C, ψ z * Q k z ∂ν) -
        (1 / 2 : ℝ) * (∫ z in C, ψ z * S k z ∂ν) +
        ∫ z in C, V z * f k z ∂ν := by
      rw [← _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := C) (fun z hz => ?_)]
      · have heq : (fun z => ((1 / 2 : ℝ) * Q k z - (1 / 2 : ℝ) * S k z +
            f k z / (2 * z.2)) * ψ z) =
            fun z => (1 / 2 : ℝ) * (ψ z * Q k z) -
              (1 / 2 : ℝ) * (ψ z * S k z) + V z * f k z := by
          funext z
          dsimp only [V]
          ring
        have hQscaled : _root_.MeasureTheory.Integrable (fun z => (1 / 2 : ℝ) * (ψ z * Q k z))
            (ν.restrict C) := hQi.const_mul _
        have hSscaled : _root_.MeasureTheory.Integrable (fun z => (1 / 2 : ℝ) * (ψ z * S k z))
            (ν.restrict C) := hSi.const_mul _
        have hdiff : _root_.MeasureTheory.Integrable (fun z => (1 / 2 : ℝ) * (ψ z * Q k z) -
            (1 / 2 : ℝ) * (ψ z * S k z)) (ν.restrict C) := hQscaled.sub hSscaled
        rw [heq, _root_.MeasureTheory.integral_add hdiff hVi, _root_.MeasureTheory.integral_sub hQscaled hSscaled,
          _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
      · have hn : z ∉ tsupport ψ := fun h => hz (hψC h)
        rw [image_eq_zero_of_notMem_tsupport hn, _root_.MulZeroClass.mul_zero]
    rw [hleft]
    calc
      _ = ∫ z, ((1 / 2 : ℝ) * Q k z - (1 / 2 : ℝ) * S k z +
          f k z / (2 * z.2)) * ψ z ∂ν := by
        simpa only [hscalarEq] using hk
      _ = _ := hright
  have hrightLim := ((henergy.const_mul (1 / 2 : ℝ)).sub
    (hscalar.const_mul (1 / 2 : ℝ))).add hzero
  have heq := tendsto_nhds_unique hlinear (hrightLim.congr' (hid.mono fun _ h => h.symm))
  change (∫ z in C, f₀ z * dψ z ∂ν) = _
  calc
    _ = ∫ z in C, dψ z * f₀ z ∂ν :=
      _root_.MeasureTheory.integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    _ = _ := heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_weak_hamilton_jacobi then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_weak_hamilton_jacobi"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_weak_hamilton_jacobi ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.poleEndpoint_redLength_limit_weak_hamilton_jacobi

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
