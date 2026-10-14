import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointWeightedRadialFluxLimit
import Submission.DifferentialGeometry.Analysis.Integration.Integral.WeightedFluxLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointSelectedDensityIntegrable
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineCutoffMass
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.CutoffLimit
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.Compact

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

private theorem integrable_deriv_and_integral_eq_zero_of_tsupport
    {η : ℝ → ℝ} {a c : ℝ} (hac : a ≤ c)
    (hη : ContDiff ℝ 1 η) (hηsupp : tsupport η ⊆ _root_.Set.Ioo a c) :
    _root_.MeasureTheory.Integrable (deriv η) (volume.restrict (_root_.Set.Ioc a c)) ∧
      (∫ t in _root_.Set.Ioc a c, deriv η t) = 0 ∧
      _root_.MeasureTheory.Integrable (fun t : _root_.Set.Ioo a c => deriv η (t : ℝ)) ∧
      (∫ t : _root_.Set.Ioo a c, deriv η (t : ℝ)) = 0 := by
  have hηa : η a = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ha => (lt_irrefl a) (hηsupp ha).1)
  have hηc : η c = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hc => (lt_irrefl c) (hηsupp hc).2)
  have hD : IntervalIntegrable (deriv η) _root_.MeasureTheory.MeasureSpace.volume a c :=
    hη.continuous_deriv_one.intervalIntegrable a c
  have hDIoc : _root_.MeasureTheory.IntegrableOn (deriv η) (_root_.Set.Ioc a c) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hac).mp hD
  have hDIoo : _root_.MeasureTheory.IntegrableOn (deriv η) (_root_.Set.Ioo a c) volume :=
    hDIoc.mono_set _root_.Set.Ioo_subset_Ioc_self
  have hzero : (∫ t in _root_.Set.Ioc a c, deriv η t) = 0 := by
    rw [← intervalIntegral.integral_of_le hac,
      intervalIntegral.integral_deriv_eq_sub (fun _ _ => hη.differentiable one_ne_zero _) hD,
      hηa, hηc, sub_self]
  have hDsub : _root_.MeasureTheory.Integrable (fun t : _root_.Set.Ioo a c => deriv η (t : ℝ)) := by
    exact (_root_.MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioo).mp hDIoo
  refine ⟨hDIoc, hzero, hDsub, ?_⟩
  calc
    (∫ t : _root_.Set.Ioo a c, deriv η (t : ℝ)) = ∫ t in _root_.Set.Ioo a c, deriv η t :=
      _root_.MeasureTheory.integral_subtype measurableSet_Ioo (deriv η)
    _ = ∫ t in _root_.Set.Ioc a c, deriv η t := integral_Ioc_eq_integral_Ioo.symm
    _ = 0 := hzero

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_deriv_and_integral_eq_zero_of_tsupport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_deriv_and_integral_eq_zero_of_tsupport target :: scope.openDecls } }

private theorem integrable_and_integral_time_transport {a c : ℝ}
    (f : ℝ → ℝ) (fI : _root_.Set.Ioo a c → ℝ)
    (hmatch : ∀ t : _root_.Set.Ioo a c, fI t = f (t : ℝ)) :
    (_root_.MeasureTheory.Integrable f (volume.restrict (_root_.Set.Ioc a c)) ↔ _root_.MeasureTheory.Integrable fI _root_.MeasureTheory.MeasureSpace.volume) ∧
      (∫ t in _root_.Set.Ioc a c, f t) = ∫ t : _root_.Set.Ioo a c, fI t := by
  have hfun : fI = (fun t : _root_.Set.Ioo a c => f (t : ℝ)) := funext hmatch
  subst fI
  constructor
  · rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    exact _root_.MeasureTheory.integrableOn_iff_comap_subtypeVal measurableSet_Ioo
  · rw [_root_.MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact (_root_.MeasureTheory.integral_subtype measurableSet_Ioo f).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_integral_time_transport
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.integrable_and_integral_time_transport target :: scope.openDecls } }

theorem tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass
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
      ({ P with metric := co.gInf (1 - s) } : PointedRiemannianManifold (I := I)))
    (ellG : P.M × ℝ → ℝ)
    (hagree : ∀ (s : _root_.Set.Ioo a c) (x : P.M),
      ellG (x, (s : ℝ)) = ell (x, ⟨(s : ℝ), ha.trans s.property.1.le⟩))
    (m : ℝ)
    (hmass : ∀ᵐ s : _root_.Set.Ioo a c, (∫ y,
      Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ))) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) = m)
    (z : P.M) (eta : ℝ → ℝ) (heta : ContDiff ℝ 1 eta)
    (hetasupp : tsupport eta ⊆ _root_.Set.Ioo a c)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {radii : ι → ℝ} (hradii : _root_.Filter.Tendsto radii l _root_.Filter.atTop) :
    let residual := fun (i : ι) (s : ℝ) (y : P.M) =>
      Real.exp (-ellG (y, s) -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log s -
        ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (deriv (fun t => eta t * radialDistanceCutoff (co.gInf (1 - a)) z (radii i) y) s +
          (co.gInf (1 - s)).inner y
            (gradientFun (co.gInf (1 - s)) (fun x => ellG (x, s)) y)
            (gradientFun (co.gInf (1 - s))
              (fun x => eta s * radialDistanceCutoff (co.gInf (1 - a)) z (radii i) x) y))
    _root_.Filter.Tendsto (fun i => ∫ s in _root_.Set.Ioc a c, ∫ y, residual i s y
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s))) l (𝓝 0) ∧
      ∀ᶠ i in l,
        (∀ᵐ s ∂volume.restrict (_root_.Set.Ioc a c), _root_.MeasureTheory.Integrable (residual i s)
          (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s)))) ∧
        _root_.MeasureTheory.Integrable (fun s => ∫ y, residual i s y
          ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - s)))
          (volume.restrict (_root_.Set.Ioc a c)) := by
  intro residual
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : _root_.MeasureTheory.IsFiniteMeasure (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (_root_.Set.Ioo a c)) := ⟨by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
    exact measure_Ioo_lt_top⟩
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Ioc a c)
  let g : ℝ → SmoothRiemannianMetric I P.M := fun s => co.gInf (1 - s)
  let ν : ℝ → _root_.MeasureTheory.Measure P.M := fun s => riemannianVolumeMeasure (I := I) (M := P.M) (g s)
  let w : ℝ × P.M → ℝ := fun v => Real.exp (-ellG (v.2, v.1) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log v.1 -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let X : ℝ → (y : P.M) → TangentSpace I y :=
    fun s => gradientFun (g s) (fun x => ellG (x, s))
  let χ : ι → P.M → ℝ := fun i => radialDistanceCutoff (co.gInf (1 - a)) z (radii i)
  let ellS : _root_.Set.Ioo a c → P.M → ℝ := fun s y =>
    ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))
  let u : _root_.Set.Ioo a c → P.M → ℝ := fun s y => Real.exp (-ellS s y -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
    ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let flux : ι → _root_.Set.Ioo a c → P.M → ℝ := fun i s y =>
    u s y * (g s).inner y (gradientFun (g s) (ellS s) y) (gradientFun (g s) (χ i) y)
  have hw (s : _root_.Set.Ioo a c) : (fun y => w ((s : ℝ), y)) = u s := by
    funext y
    dsimp only [w, u, ellS]
    rw [hagree s y]
  have hw_apply (s : _root_.Set.Ioo a c) (y : P.M) : w ((s : ℝ), y) = u s y :=
    congrFun (hw s) y
  have hX (s : _root_.Set.Ioo a c) : X s = gradientFun (g s) (ellS s) := by
    have hslices : (fun y => ellG (y, (s : ℝ))) = ellS s := funext (hagree s)
    dsimp only [X]
    rw [hslices]
  have hflux (i : ι) (s : _root_.Set.Ioo a c) :
      (fun y => w ((s : ℝ), y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y)) =
        flux i s := by
    change (fun y => (fun x => w ((s : ℝ), x)) y *
      (g s).inner y (X s y) (gradientFun (g s) (χ i) y)) = _
    rw [hw s, hX s]
  have hu (s : _root_.Set.Ioo a c) : _root_.MeasureTheory.Integrable (u s) (ν s) :=
    co.integrable_poleEndpoint_redDensity_of_redLength F hcar hreg b hbmem tau q hsigma
      Phi kappa hancient p hbase psi hpsi ell hconv
      (ha.trans s.property.1.le) (hcomplete s ⟨s.property.1.le, s.property.2.le⟩)
  have hwSpatial : ∀ᵐ s ∂μ, _root_.MeasureTheory.Integrable (fun y => w (s, y)) (ν s) := by
    dsimp only [μ]
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    apply (ae_restrict_iff_subtype measurableSet_Ioo).2
    exact Eventually.of_forall fun s => by rw [hw s]; exact hu s
  have hwnonneg : ∀ᵐ s ∂μ, ∀ᵐ y ∂ν s, 0 ≤ w (s, y) :=
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => Real.exp_nonneg _
  have hwMass : ∀ᵐ s ∂μ, (∫ y, w (s, y) ∂ν s) = m := by
    dsimp only [μ]
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    apply (ae_restrict_iff_subtype measurableSet_Ioo).2
    filter_upwards [hmass] with s hs
    rw [hw s]
    exact hs
  have hpos : ∀ᶠ i in l, 0 < radii i := hradii.eventually (_root_.Filter.eventually_gt_atTop 0)
  have hχmeas : ∀ᶠ i in l, Measurable (χ i) := hpos.mono fun i hi =>
    (continuous_radialDistanceCutoff (co.gInf (1 - a)) z hi).measurable
  have hχbound : ∀ᶠ i in l, ∀ y, ‖χ i y‖ ≤ 1 := hpos.mono fun i hi y => by
    obtain ⟨hzero, hone⟩ := radialDistanceCutoff_mem_Icc (co.gInf (1 - a)) z hi y
    rw [Real.norm_of_nonneg hzero]
    exact hone
  have hχone : ∀ y, _root_.Filter.Tendsto (fun i => χ i y) l (𝓝 1) :=
    tendsto_radialDistanceCutoff (co.gInf (1 - a)) z hradii
  obtain ⟨hD, hDzero, _, _⟩ :=
    integrable_deriv_and_integral_eq_zero_of_tsupport hac heta hetasupp
  obtain ⟨tmax, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hac) heta.continuous.norm.continuousOn
  let K : ℝ := ‖eta tmax‖
  have hetaBound : ∀ᵐ s : _root_.Set.Ioo a c, |eta (s : ℝ)| ≤ K := Eventually.of_forall fun s => by
    exact hmax ⟨s.property.1.le, s.property.2.le⟩
  have hetaNormBound : ∀ᵐ s : _root_.Set.Ioo a c, ‖eta (s : ℝ)‖ ≤ K := hetaBound
  have hetaMeas : _root_.MeasureTheory.AEStronglyMeasurable (fun s : _root_.Set.Ioo a c => eta (s : ℝ)) volume :=
    (heta.continuous.comp continuous_subtype_val).aestronglyMeasurable
  have hmassMeas : ∀ᶠ i in l,
      AEStronglyMeasurable (fun s => ∫ y, χ i y * w (s, y) ∂ν s) μ := by
    filter_upwards [hpos, hχbound] with i hi hbi
    have hmI : _root_.MeasureTheory.AEStronglyMeasurable (fun s : _root_.Set.Ioo a c => ∫ y, χ i y * u s y ∂ν s) volume :=
      co.aestronglyMeasurable_integral_radialDistanceCutoff_mul_exp Phi
        (fun _ ht => ht) ha _root_.MeasureTheory.MeasureSpace.volume ell z hi
    have hbI : ∀ᵐ s : _root_.Set.Ioo a c, ‖∫ y, χ i y * u s y ∂ν s‖ ≤ m := by
      filter_upwards [hmass] with s hms
      have hnormmass : (∫ y, ‖u s y‖ ∂ν s) = m := by
        calc
          (∫ y, ‖u s y‖ ∂ν s) = ∫ y, u s y ∂ν s := by
            apply _root_.MeasureTheory.integral_congr_ae
            exact Eventually.of_forall fun y => Real.norm_of_nonneg (Real.exp_nonneg _)
          _ = m := hms
      rw [← hnormmass]
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le (hu s).norm
      exact Eventually.of_forall fun y => by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hbi y)
    have hmInt : _root_.MeasureTheory.Integrable (fun s : _root_.Set.Ioo a c => ∫ y, χ i y * u s y ∂ν s) volume :=
      Integrable.of_bound hmI m hbI
    have htr := integrable_and_integral_time_transport
      (fun s => ∫ y, χ i y * w (s, y) ∂ν s)
      (fun s : _root_.Set.Ioo a c => ∫ y, χ i y * u s y ∂ν s)
      (fun s => by simp_rw [hw_apply s])
    exact (htr.1.mpr hmInt).aestronglyMeasurable
  obtain ⟨_, _, hfluxInt⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  have hfluxSpatial : ∀ᶠ i in l, ∀ᵐ s ∂μ,
      _root_.MeasureTheory.Integrable (fun y => eta s *
        (w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y))) (ν s) := by
    filter_upwards [hpos] with i hi
    dsimp only [μ]
    rw [← _root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    apply (ae_restrict_iff_subtype measurableSet_Ioo).2
    apply Eventually.of_forall
    intro s
    have hfi : _root_.MeasureTheory.Integrable (flux i s) (ν s) := (hfluxInt z (radii i) hi).1 s
    have hscaled := hfi.const_mul (eta s)
    simpa only [← hflux i s] using hscaled
  have hfluxTime : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (fun s => eta s *
      (∫ y, w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s)) μ := by
    filter_upwards [hpos] with i hi
    have hfi : _root_.MeasureTheory.Integrable (fun s : _root_.Set.Ioo a c => ∫ y, flux i s y ∂ν s) volume :=
      (hfluxInt z (radii i) hi).2.1
    have hweighted := hfi.bdd_mul hetaMeas hetaNormBound
    exact (integrable_and_integral_time_transport
      (fun s => eta s * (∫ y, w (s, y) *
        (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s))
      (fun s : _root_.Set.Ioo a c => eta s * ∫ y, flux i s y ∂ν s)
      (fun s => by rw [hflux i s])).1.mpr hweighted
  have hfluxLimI := co.tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux
    F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
    ha hac hcomplete z (fun s : _root_.Set.Ioo a c => eta (s : ℝ))
    hetaMeas hetaBound hradii
  have hfluxLim : _root_.Filter.Tendsto (fun i => ∫ s, eta s *
      (∫ y, w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s) ∂μ)
      l (𝓝 0) := by
    have heq : (fun i => ∫ s, eta s *
        (∫ y, w (s, y) * (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s) ∂μ) =
        (fun i => ∫ s : _root_.Set.Ioo a c, eta s * ∫ y, flux i s y ∂ν s) := by
      funext i
      exact (integrable_and_integral_time_transport
        (fun s => eta s * (∫ y, w (s, y) *
          (g s).inner y (X s y) (gradientFun (g s) (χ i) y) ∂ν s))
        (fun s : _root_.Set.Ioo a c => eta s * ∫ y, flux i s y ∂ν s)
        (fun s => by rw [hflux i s])).2
    rw [heq]
    exact hfluxLimI
  have hmain :=
    integrable_and_tendsto_integral_integral_parabolic_test_residual_prod_zero_of_const_mass
    μ ν g w X eta χ hχmeas hχbound hχone hwSpatial hwnonneg m hwMass
    hD hDzero hmassMeas hfluxSpatial hfluxTime hfluxLim
  exact ⟨hmain.2, hmain.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_poleEndpoint_radialDistanceCutoff_residual_of_const_mass

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
