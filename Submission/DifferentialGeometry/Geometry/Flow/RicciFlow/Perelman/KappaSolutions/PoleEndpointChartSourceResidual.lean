import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.ChartResidualTransport
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.GaussianIntegrability
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.CompactTestExtension
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSourceResidual
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityLipschitz
import Submission.DifferentialGeometry.Analysis.Calculus.GaussianNormalization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineTimeReversal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }
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
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM : MeasurableSpace F.M := borel F.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM : BorelSpace F.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM_1 : MeasurableSpace P.M := borel P.M

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instMeasurableSpaceM_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM_1 : BorelSpace P.M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instBorelSpaceM_1 target :: scope.openDecls } }

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace HalfLineMetricConvergenceData

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instMeasurableSpaceEuclideanSpaceRealFinFinrank : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instMeasurableSpaceEuclideanSpaceRealFinFinrank
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instMeasurableSpaceEuclideanSpaceRealFinFinrank target :: scope.openDecls } }

private theorem locallyLipschitzOn_comp_lipschitzWith
    {X₁ X₂ X₃ : Type*} [PseudoEMetricSpace X₁] [PseudoEMetricSpace X₂]
    [PseudoEMetricSpace X₃]
    {S : Set X₁} {T : Set X₂} {f : X₂ → X₃} {g : X₁ → X₂} {C : NNReal}
    (hf : LocallyLipschitzOn T f) (hg : LipschitzWith C g) (hmap : _root_.Set.MapsTo g S T) :
    LocallyLipschitzOn S (f ∘ g) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hf.restrict.comp (hg.lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.locallyLipschitzOn_comp_lipschitzWith
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.locallyLipschitzOn_comp_lipschitzWith target :: scope.openDecls } }

theorem integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (hb : b < 0) {kappa0 : ℝ}
    (hAncient : IsAncientKappaSolution kappa0 F)
    (p : F.M) {a c A : ℝ} (ha : 1 < a)
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop _root_.Filter.atTop) (hphi : StrictMono phi)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ellC : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ellC _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hagree : ∀ (y : P.M) (t : ℝ) (ht : 1 ≤ t), ell (y, t) = ellC (y, ⟨t, ht⟩))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (hcompleteOn : ∀ t ∈ _root_.Set.Icc a' c', MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold (I := I)))
    (x : P.M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target)
    (ψ : ℝ × E → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ _root_.Set.Ioo a' c' ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω)) :
    let f : ℝ × E → ℝ := fun z => ell ((extChartAt I x).symm z.2, z.1)
    let u : ℝ × E → ℝ := fun z => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    (∫ z, chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
      (deriv (fun t => ψ (t, z.2)) z.1 +
        chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
          (fderiv ℝ (fun y => f (z.1, y)) z.2)
          (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
      ∂(Measure.prod (Measure.restrict _root_.MeasureTheory.MeasureSpace.volume (_root_.Set.Ioc a' c'))
        (Measure.restrict (modelHaar (E := E)) ((toEuclidean (E := E)) ⁻¹' Ω)))) = 0 := by
  intro f u
  let e := toEuclidean (E := E)
  let W : Set E := e ⁻¹' Ω
  let K : Set E := e.symm '' closure Ω
  let J : Set P.M := (extChartAt I x).symm '' K
  have hK : IsCompact K := hΩc.image e.symm.continuous
  have hJ : IsCompact J := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := I) x).mono hΩt)
  have hKt : K ⊆ (extChartAt I x).target := hΩt
  have hKJ : _root_.Set.MapsTo (extChartAt I x).symm K J := fun y hy => ⟨y, hy, rfl⟩
  have hWK : W ⊆ K := by
    intro y hy
    exact ⟨e y, subset_closure hy, e.symm_apply_apply y⟩
  have hW : IsOpen W := hΩ.preimage e.continuous
  have hWt : W ⊆ (extChartAt I x).target := hWK.trans hKt
  have hbaseSelected : ∀ᶠ k in _root_.Filter.atTop,
      redLength ((U).term (phi (co.φ k))).S 0 p (q (phi (co.φ k))) 1 ≤ A :=
    Eventually.of_forall fun k => hbase (phi (co.φ k))
  have hconvPointwise : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (psi k)))).S 0 p
        (Phi.map (co.φ (psi k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))) := by
    intro y _ t ht
    have htOne : 1 ≤ t := ha.le.trans ht.1
    have hpt := hconv.tendstoLocallyUniformlyOn.tendsto_at
      (_root_.Set.mem_univ (y, (⟨t, htOne⟩ : _root_.Set.Ici (1 : ℝ))))
    rw [hagree y t htOne]
    exact hpt
  have hfChart : LocallyLipschitzOn (_root_.Set.Icc a c ×ˢ K) f :=
    locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbaseSelected
      psi hpsi.tendsto_atTop ell hconvPointwise x hKt hKJ
  let T : ℝ × EuStd → ℝ × E := fun v => (v.1, e.symm v.2)
  have hT : LipschitzWith (_root_.Max.max 1 ‖e.symm.toContinuousLinearMap‖₊) T := by
    simpa only [mul_one, T, Function.comp_def] using
      (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × EuStd → ℝ)).prodMk
        (e.symm.lipschitz.comp
          (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × EuStd → EuStd)))
  have hfV : LocallyLipschitzOn (_root_.Set.Icc a' c' ×ˢ closure Ω)
      (fun v : ℝ × EuStd => f (v.1, e.symm v.2)) := by
    apply locallyLipschitzOn_comp_lipschitzWith hfChart hT
    intro v hv
    exact ⟨⟨haa.le.trans hv.1.1, hv.1.2.trans hcc.le⟩, ⟨v.2, hv.2, rfl⟩⟩
  have huV : LocallyLipschitzOn (_root_.Set.Icc a' c' ×ˢ closure Ω)
      (fun v : ℝ × EuStd => u (v.1, e.symm v.2)) :=
    locallyLipschitzOn_exp_gaussian_normalization (zero_lt_one.trans (ha.trans haa))
      hfV (Module.finrank ℝ E)
  let Dτ := RealTimeInterval.openInfinite 1 a ha
  have hYreg : _root_.Set.Iio 0 ⊆ (Y).D.regular := fun _ ht => ht
  have hg : MetricFamilySmoothOn (I := I) Dτ (fun t => co.gInf (1 - t)) :=
    co.metric_smooth_time_sub (Φ := Phi) hYreg 1 (fun _ ht => ht)
  have hinterval : _root_.Set.Icc a' c' ⊆ Dτ.regular := fun _ ht => (ha.trans haa).trans_le ht.1
  have hΩtV : closure Ω ⊆
      DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid (I := I) x := by
    intro v hv
    exact ⟨e.symm v, hKt ⟨v, hv, rfl⟩, e.apply_symm_apply v⟩
  let φ : ℝ × EuStd → ℝ := ψ ∘ T
  have hφ : ContDiff ℝ 1 φ :=
    (hψ.of_le (by simp)).comp
      (contDiff_fst.prodMk (e.symm.contDiff.comp contDiff_snd))
  have htest (t : ℝ) (y : E) : φ (t, e y) = ψ (t, y) := by
    simp only [φ, T, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply]
  have htestTime (y : E) : (fun t => φ (t, e y)) = fun t => ψ (t, y) :=
    funext fun t => htest t y
  have htestSpace (t : ℝ) : (fun y => φ (t, e y)) = fun y => ψ (t, y) :=
    funext fun y => htest t y
  have hi : MeasureTheory.Integrable (fun z : ℝ × E =>
      chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2)))
      (Measure.prod (Measure.restrict _root_.MeasureTheory.MeasureSpace.volume (_root_.Set.Ioc a' c'))
        (Measure.restrict (modelHaar (E := E)) W)) := by
    simpa only [φ, T, e, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply, W] using
      integrable_chartGaussianResidual_of_locallyLipschitzOn Dτ
        (fun t => co.gInf (1 - t)) hg x hinterval hΩ hΩc hΩtV hfV huV hφ
  obtain ⟨Ψ, hΨ, hΨc, hΨs, hΨW, hext⟩ :=
    exists_contMDiff_hasCompactSupport_chart_extension x hψ hψc hψsupp hWt
  have hΨsource : Prod.snd '' tsupport Ψ ⊆ (chartAt H x).source := by
    rintro y ⟨z, hz, rfl⟩
    exact (hΨs hz).2
  have hΨtime : tsupport Ψ ⊆ _root_.Set.Ioo a' c' ×ˢ (_root_.Set.univ : Set P.M) :=
    fun z hz => ⟨(hΨs hz).1, _root_.Set.mem_univ _⟩
  have hzero := co.integral_poleEndpoint_redDensity_limit_residual_eq_zero_of_ancient_of_contMDiff
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt
      hcomplete hboundary kappa hF hb hAncient p ha hbase hescape hphi
      psi hpsi ellC hconv ell hagree haa hac hcc hcompleteOn
      Ψ (hΨ.of_le (by simp)) hΨc hΨtime
  let uM : ℝ × P.M → ℝ := fun z => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let fM : ℝ × P.M → ℝ := fun z => ell (z.2, z.1)
  have hfInner : LocallyLipschitzOn (_root_.Set.Ioo a' c' ×ˢ W)
      (fun z : ℝ × E => fM (z.1, (extChartAt I x).symm z.2)) :=
    hfChart.mono fun z hz =>
      ⟨⟨(haa.trans hz.1.1).le, (hz.1.2.trans hcc).le⟩, hWK hz.2⟩
  have hψLip : LocallyLipschitzOn (_root_.Set.Ioo a' c' ×ˢ W) ψ :=
    (hψ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).locallyLipschitz.locallyLipschitzOn
  have htransport := integral_chart_time_gradient_residual_eq_of_extension
    (fun t => co.gInf (1 - t)) x uM fM Ψ ψ hW hWt hΨc hΨsource hΨW
      (fun t y hy => hext t y (hWt hy)) hfInner hψLip hi
  exact htransport.trans hzero.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integral_poleEndpoint_redDensity_limit_chart_residual_eq_zero_of_ancient

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
