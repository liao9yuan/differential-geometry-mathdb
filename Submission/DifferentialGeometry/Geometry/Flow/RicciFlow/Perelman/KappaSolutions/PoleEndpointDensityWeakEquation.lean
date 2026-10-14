import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityLipschitz
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.GaussianDensity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineTimeReversal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

private theorem locallyLipschitzOn_comp_lipschitzWith
    {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {S : Set X} {T : Set Y} {f : Y → Z} {g : X → Y} {C : NNReal}
    (hf : LocallyLipschitzOn T f) (hg : LipschitzWith C g) (hmap : Set.MapsTo g S T) :
    LocallyLipschitzOn S (f ∘ g) := by
  apply locallyLipschitzOn_iff_restrict.mpr
  exact hf.restrict.comp (hg.lipschitzOnWith.mapsToRestrict hmap).locallyLipschitz

run_cmd do
  let target := ``Submission.locallyLipschitzOn_comp_lipschitzWith
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `locallyLipschitzOn_comp_lipschitzWith target :: scope.openDecls } }

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
  (spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn)
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
  (exists_lp_weak_equation_exp_gaussian_of_chartResidual_eq_zero)
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
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

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instMeasurableSpaceEuclideanSpaceRealFinFinrank : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instMeasurableSpaceEuclideanSpaceRealFinFinrank
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.instMeasurableSpaceEuclideanSpaceRealFinFinrank target :: scope.openDecls } }

theorem exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    (hR : RiemannianMetricComplete R)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {A a c : ℝ} (ha : 1 < a)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0 p
      (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y ∈ J, ∀ t ∈ _root_.Set.Icc a c,
      _root_.Filter.Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) _root_.Filter.atTop (𝓝 (ell (y, t))))
    (x : P.M) {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩt : (toEuclidean (E := E)).symm '' closure Ω ⊆ (extChartAt I x).target)
    (hΩJ : _root_.Set.MapsTo (extChartAt I x).symm ((toEuclidean (E := E)).symm '' closure Ω) J) :
    let ν := (volume.restrict (_root_.Set.Icc a c)).prod (volume.restrict Ω)
    let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
    let u := fun z : ℝ × E => Real.exp (-f z -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let uV := fun v : ℝ × EuStd => u (v.1, (toEuclidean (E := E)).symm v.2)
    (∀ ψ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ _root_.Set.Ioo a c ×ˢ ((toEuclidean (E := E)) ⁻¹' Ω) →
      (∫ z, chartDensity (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2) * u z *
        (deriv (fun t => ψ (t, z.2)) z.1 +
          chartGradientBilin (co.gInf (1 - z.1)) x ((extChartAt I x).symm z.2)
            (fderiv ℝ (fun y => f (z.1, y)) z.2)
            (fderiv ℝ (fun y => ψ (z.1, y)) z.2))
        ∂(volume.restrict (_root_.Set.Ioc a c)).prod
          ((modelHaar (E := E)).restrict ((toEuclidean (E := E)) ⁻¹' Ω))) = 0) →
    ∃ V : _root_.MeasureTheory.Lp ℝ 2 ν, ∃ K : Fin (Module.finrank ℝ E) → _root_.MeasureTheory.Lp ℝ 2 ν,
      (V =ᵐ[ν] uV) ∧
      (∀ i, K i =ᵐ[ν] fun v =>
        fderiv ℝ (fun y => uV (v.1, y)) v.2 (EuclideanSpace.single i 1)) ∧
      (∀ i, K i =ᵐ[ν] fun v => -uV v *
        fderiv ℝ (fun y => f (v.1, (toEuclidean (E := E)).symm y)) v.2
          (EuclideanSpace.single i 1)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a c), DeGiorgi.HasWeakPartialDeriv i
        (fun y => K i (t, y)) (fun y => V (t, y)) Ω) ∧
      ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a c ×ˢ Ω →
        (∫ v, densityOnEuclid (co.gInf (1 - v.1)) x v.2 * V v *
          fderiv ℝ φ v (1, 0) ∂ν) =
            ∑ j, ∫ v, (∑ i, weightedInvGramOnEuclid
              (co.gInf (1 - v.1)) x i j v.2 * K i v) *
                fderiv ℝ φ v (0, EuclideanSpace.single j 1) ∂ν := by
  intro ν f u uV hresidual
  let W := (toEuclidean (E := E)).symm '' closure Ω
  have hfchart := locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
    F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hancient p hJ ha.le hbase
      rho hrho ell hconv x hΩt hΩJ
  let T : ℝ × EuStd → ℝ × E := fun v => (v.1, (toEuclidean (E := E)).symm v.2)
  have hT : LipschitzWith (_root_.Max.max 1 ‖(toEuclidean (E := E)).symm.toContinuousLinearMap‖₊) T :=
    by
      simpa only [mul_one, T, Function.comp_def] using
        (LipschitzWith.prod_fst : LipschitzWith 1 (Prod.fst : ℝ × EuStd → ℝ)).prodMk
          ((toEuclidean (E := E)).symm.lipschitz.comp
            (LipschitzWith.prod_snd : LipschitzWith 1 (Prod.snd : ℝ × EuStd → EuStd)))
  have hmaps : _root_.Set.MapsTo T (_root_.Set.Icc a c ×ˢ closure Ω) (_root_.Set.Icc a c ×ˢ W) :=
    fun v hv => ⟨hv.1, ⟨v.2, hv.2, rfl⟩⟩
  have hf : LocallyLipschitzOn (_root_.Set.Icc a c ×ˢ closure Ω)
      (fun v : ℝ × EuStd => f (v.1, (toEuclidean (E := E)).symm v.2)) := by
    simpa only [Function.comp_def, T, f] using
      locallyLipschitzOn_comp_lipschitzWith hfchart hT hmaps
  let Dτ := RealTimeInterval.openInfinite 1 a ha
  have hYreg : _root_.Set.Iio 0 ⊆ (Y).D.regular := by
    change _root_.Set.Iio 0 ⊆ ancientTimeInterval.regular
    rw [ancientTimeInterval_regular]
  have hg : MetricFamilySmoothOn (I := I) Dτ (fun t => co.gInf (1 - t)) :=
    co.metric_smooth_time_sub (Φ := Phi) hYreg 1 (fun _ ht => ht)
  have hinterval : _root_.Set.Icc a c ⊆ Dτ.regular := fun _ ht => ha.trans_le ht.1
  have hΩtV : closure Ω ⊆ chartTargetEuclid (I := I) x := by
    intro v hv
    exact ⟨(toEuclidean (E := E)).symm v, hΩt ⟨v, hv, rfl⟩,
      (toEuclidean (E := E)).apply_symm_apply v⟩
  obtain ⟨V, K, hV, hK, hspatial, hweak⟩ :=
    exists_lp_weak_equation_exp_gaussian_of_chartResidual_eq_zero Dτ
      (fun t => co.gInf (1 - t)) hg x (zero_lt_one.trans ha) hinterval
      hΩ hΩc hΩtV f (Module.finrank ℝ E) hf hresidual
  refine ⟨V, K, hV, hK, ?_, hspatial, hweak⟩
  intro i
  exact (hK i).trans
    (spatial_fderiv_exp_gaussian_normalization_ae_of_locallyLipschitzOn
      (zero_lt_one.trans ha) hΩ hΩc hf (Module.finrank ℝ E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_lp_weak_equation_poleEndpoint_redDensity_limit_of_chartResidual_eq_zero

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
