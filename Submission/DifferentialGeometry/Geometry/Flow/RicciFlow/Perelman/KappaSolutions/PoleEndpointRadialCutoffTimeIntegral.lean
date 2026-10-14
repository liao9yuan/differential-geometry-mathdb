import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointRadialCutoffFluxIntegrable
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GradientFlux
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineGramContinuity
import Submission.DifferentialGeometry.Geometry.Metric.Distance.RadialCutoff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

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

private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }
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

private theorem continuousOn_chartGramMatrix_time_sub
    {X : PointedFlowSeq (I := I)} (Phi : PointedCGHMaps X P phi)
    {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : _root_.Set.Iic (0 : ℝ) ⊆ X.D.carrier) {a c : ℝ} (ha : 1 ≤ a)
    (alpha : P.M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun v : _root_.Set.Ioo a c × P.M =>
      Tensor.Coordinates.chartGramMatrix (co.gInf (1 - (v.1 : ℝ))) alpha v.2 i j)
      (_root_.Set.univ ×ˢ (chartAt H alpha).source) := by
  have hc := continuousOn_chartGramMatrix
    (I := I) (X := X) (P := P) (phi := phi) Phi
    (R := R) (bf := bf) (hsrc := hsrc) (htgt := htgt) co hcarrier alpha i j
  have hmap : Continuous (fun v : _root_.Set.Ioo a c × P.M => (1 - (v.1 : ℝ), v.2)) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  have hmaps : _root_.Set.MapsTo (fun v : _root_.Set.Ioo a c × P.M => (1 - (v.1 : ℝ), v.2))
      (_root_.Set.univ ×ˢ (chartAt H alpha).source)
      (_root_.Set.Iic (0 : ℝ) ×ˢ (chartAt H alpha).source) := by
    intro v hv
    exact ⟨sub_nonpos.mpr (ha.trans v.1.property.1.le), hv.2⟩
  have hcomp := ContinuousOn.comp'
    (g := fun q : ℝ × P.M =>
      Tensor.Coordinates.chartGramMatrix (co.gInf q.1) alpha q.2 i j)
    (f := fun v : _root_.Set.Ioo a c × P.M => (1 - (v.1 : ℝ), v.2))
    (s := _root_.Set.univ ×ˢ (chartAt H alpha).source)
    (t := _root_.Set.Iic (0 : ℝ) ×ˢ (chartAt H alpha).source)
    hc hmap.continuousOn hmaps
  exact hcomp

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartGramMatrix_time_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.continuousOn_chartGramMatrix_time_sub target :: scope.openDecls } }

private theorem integrable_integral_gaussian_gradient_pairing
    {a c : ℝ} (ha : 1 ≤ a) (qref : SmoothRiemannianMetric I P.M)
    (G : _root_.Set.Ioo a c → SmoothRiemannianMetric I P.M)
    (ell : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ)) (cutoff : P.M → ℝ) (hcutoff : Continuous cutoff)
    (hgram : ∀ (alpha : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun v : _root_.Set.Ioo a c × P.M =>
        Tensor.Coordinates.chartGramMatrix (G v.1) alpha v.2 i j)
        (_root_.Set.univ ×ˢ (chartAt H alpha).source)) (C : ℝ)
    (hbound : ∀ s : _root_.Set.Ioo a c,
      ∫ y, |Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ))) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (G s).inner y (gradientFun (G s)
          (fun x => ell (x, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))) y)
          (gradientFun (G s) cutoff y)|
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s) ≤ C) :
    let f : _root_.Set.Ioo a c → P.M → ℝ := fun s y =>
      ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))
    let w : _root_.Set.Ioo a c × P.M → ℝ := fun v => Real.exp (-f v.1 v.2 -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (v.1 : ℝ) -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
    let flux : _root_.Set.Ioo a c → P.M → ℝ := fun s y =>
      w (s, y) * (G s).inner y (gradientFun (G s) (f s) y)
        (gradientFun (G s) cutoff y)
    _root_.MeasureTheory.Integrable (fun s => ∫ y, flux s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)) _root_.MeasureTheory.MeasureSpace.volume ∧
      |∫ s : _root_.Set.Ioo a c, ∫ y, flux s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)| ≤
        C * volume.real (_root_.Set.univ : Set (_root_.Set.Ioo a c)) := by
  intro f w flux
  have hf : Continuous (Function.uncurry f) :=
    ell.continuous.comp (continuous_snd.prodMk
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _))
  have hh : Continuous (Function.uncurry (fun _ : _root_.Set.Ioo a c => cutoff)) :=
    hcutoff.comp continuous_snd
  have hw : Continuous w := by
    have hlog : Continuous (fun v : _root_.Set.Ioo a c × P.M => Real.log (v.1 : ℝ)) :=
      (continuous_subtype_val.comp continuous_fst).log (fun v =>
        ne_of_gt (zero_lt_one.trans_le (ha.trans v.1.property.1.le)))
    exact Real.continuous_exp.comp
      ((hf.neg.sub (continuous_const.mul hlog)).sub continuous_const)
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology P.M := ChartedSpace.secondCountable_of_sigmaCompact H P.M
  let : _root_.MeasureTheory.IsFiniteMeasure (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (_root_.Set.Ioo a c)) := ⟨by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
    exact measure_Ioo_lt_top⟩
  obtain ⟨hi, hb⟩ := integrable_integral_mul_inner_gradientFun_family
    qref G _root_.MeasureTheory.MeasureSpace.volume f (fun _ => cutoff) w hf hh hgram hw.aestronglyMeasurable
    (_root_.MeasureTheory.integrable_const C) (Eventually.of_forall hbound)
  have hconst : (∫ _ : _root_.Set.Ioo a c, C) = C * volume.real (_root_.Set.univ : Set (_root_.Set.Ioo a c)) := by
    rw [_root_.MeasureTheory.integral_const, smul_eq_mul, mul_comm]
  rw [hconst] at hb
  exact ⟨hi, hb⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_integral_gaussian_gradient_pairing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_integral_gaussian_gradient_pairing target :: scope.openDecls } }

theorem exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (kappa : ℕ → ℝ) (hancient : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {A : ℝ}
    (hbase : ∀ i, redLength ((U).term i).S 0 p (q i) 1 ≤ A)
    (psi : ℕ → ℕ) (hpsi : StrictMono psi) (ell : C(P.M × _root_.Set.Ici (1 : ℝ), ℝ))
    (hconv : TendstoLocallyUniformly
      (fun k (z : P.M × _root_.Set.Ici (1 : ℝ)) =>
        redLength ((U).term (phi (co.φ (psi k)))).S 0 p
          (Phi.map (co.φ (psi k)) z.1) z.2) ell _root_.Filter.atTop)
    {a c : ℝ} (ha : 1 ≤ a) (hac : a ≤ c)
    (hcomplete : ∀ s ∈ _root_.Set.Icc a c, MetricComplete (I := I)
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : P.M, ∀ r : ℝ, 0 < r →
      let flux := fun (s : _root_.Set.Ioo a c) (y : P.M) =>
        Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ))) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (co.gInf (1 - (s : ℝ))).inner y
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (fun x => ell (x, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))) y)
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (radialDistanceCutoff (co.gInf (1 - a)) z r) y)
      (∀ s, _root_.MeasureTheory.Integrable (flux s)
        (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ))))) ∧
      _root_.MeasureTheory.Integrable (fun s : _root_.Set.Ioo a c => ∫ y, flux s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) _root_.MeasureTheory.MeasureSpace.volume ∧
      |∫ s : _root_.Set.Ioo a c, ∫ y, flux s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))| ≤
        (C / r) * volume.real (_root_.Set.univ : Set (_root_.Set.Ioo a c)) := by
  obtain ⟨C, hC, hlintegral⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_lintegral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  obtain ⟨_, _, hspatial⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  refine ⟨C, hC, ?_⟩
  intro z r hr
  let G : _root_.Set.Ioo a c → SmoothRiemannianMetric I P.M := fun s => co.gInf (1 - (s : ℝ))
  let f : _root_.Set.Ioo a c → P.M → ℝ := fun s y =>
    ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))
  let w : _root_.Set.Ioo a c × P.M → ℝ := fun v => Real.exp (-f v.1 v.2 -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (v.1 : ℝ) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let cutoff := radialDistanceCutoff (co.gInf (1 - a)) z r
  let flux : _root_.Set.Ioo a c → P.M → ℝ := fun s y =>
    w (s, y) * (G s).inner y (gradientFun (G s) (f s) y)
      (gradientFun (G s) cutoff y)
  change (∀ s, _root_.MeasureTheory.Integrable (flux s) (riemannianVolumeMeasure (I := I) (M := P.M) (G s))) ∧
    _root_.MeasureTheory.Integrable (fun s => ∫ y, flux s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)) _root_.MeasureTheory.MeasureSpace.volume ∧
    |∫ s : _root_.Set.Ioo a c, ∫ y, flux s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)| ≤
      (C / r) * volume.real (_root_.Set.univ : Set (_root_.Set.Ioo a c))
  have hfi (s : _root_.Set.Ioo a c) : _root_.MeasureTheory.Integrable (flux s)
      (riemannianVolumeMeasure (I := I) (M := P.M) (G s)) :=
    (hspatial z ⟨(s : ℝ), ha.trans s.property.1.le⟩
      ⟨s.property.1.le, s.property.2.le⟩ r hr).1
  have hnorm (s : _root_.Set.Ioo a c) :
      (∫ y, |flux s y| ∂riemannianVolumeMeasure (I := I) (M := P.M) (G s)) ≤ C / r := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hlintegral z ⟨(s : ℝ), ha.trans s.property.1.le⟩
        ⟨s.property.1.le, s.property.2.le⟩ r hr)
    rw [ENNReal.toReal_ofReal (div_nonneg hC hr.le)] at hb
    have heq := _root_.MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y => abs_nonneg (flux s y)) (hfi s).abs.aestronglyMeasurable
    exact heq.trans_le hb
  let : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  have hcutoff : Continuous cutoff :=
    continuous_radialDistanceCutoff (co.gInf (1 - a)) z hr
  have hgram : ∀ (alpha : P.M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun v : _root_.Set.Ioo a c × P.M =>
        Tensor.Coordinates.chartGramMatrix (G v.1) alpha v.2 i j)
        (_root_.Set.univ ×ˢ (chartAt H alpha).source) :=
    fun alpha i j => continuousOn_chartGramMatrix_time_sub Phi co
      (fun _ ht => ht) ha alpha i j
  exact ⟨hfi, integrable_integral_gaussian_gradient_pairing ha
    (co.gInf (1 - a)) G ell cutoff hcutoff hgram (C / r) hnorm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
