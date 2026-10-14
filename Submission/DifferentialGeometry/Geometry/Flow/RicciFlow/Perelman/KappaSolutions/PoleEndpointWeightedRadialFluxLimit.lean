import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointRadialCutoffTimeIntegral
import Submission.DifferentialGeometry.Analysis.Integration.Integral.WeightedFluxLimit

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

theorem tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux
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
    (z : P.M) (eta : _root_.Set.Ioo a c → ℝ) (heta : _root_.MeasureTheory.AEStronglyMeasurable eta _root_.MeasureTheory.MeasureSpace.volume)
    {K : ℝ} (hetabound : ∀ᵐ s ∂volume, |eta s| ≤ K)
    {ι : Type*} {l : Filter ι} {radii : ι → ℝ} (hradii : _root_.Filter.Tendsto radii l _root_.Filter.atTop) :
    let flux := fun (r : ℝ) (s : _root_.Set.Ioo a c) (y : P.M) =>
        Real.exp (-ell (y, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ))) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (s : ℝ) -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi)) *
        (co.gInf (1 - (s : ℝ))).inner y
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (fun x => ell (x, (⟨(s : ℝ), ha.trans s.property.1.le⟩ : _root_.Set.Ici (1 : ℝ)))) y)
          (gradientFun (co.gInf (1 - (s : ℝ)))
            (radialDistanceCutoff (co.gInf (1 - a)) z r) y)
    _root_.Filter.Tendsto (fun i => ∫ s : _root_.Set.Ioo a c, eta s *
      ∫ y, flux (radii i) s y
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))) l (𝓝 0) := by
  intro flux
  obtain ⟨_, _, htime⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_time_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  obtain ⟨C, _, hspatial⟩ :=
    co.exists_uniform_redDensity_limit_radialDistanceCutoff_flux_integral_bound
      F hcar hreg b hbmem tau q hsigma Phi kappa hancient p hbase psi hpsi ell hconv
      ha hac hcomplete
  let innerFlux : ℝ → _root_.Set.Ioo a c → ℝ := fun r s => ∫ y, flux r s y
    ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf (1 - (s : ℝ)))
  have hF (r : ℝ) (hr : 0 < r) : _root_.MeasureTheory.Integrable (innerFlux r) volume :=
    (htime z r hr).2.1
  have hb (r : ℝ) (hr : 0 < r) : ∀ᵐ s ∂volume, |innerFlux r s| ≤ C / r := by
    filter_upwards [] with s
    exact (hspatial z ⟨(s : ℝ), ha.trans s.property.1.le⟩
      ⟨s.property.1.le, s.property.2.le⟩ r hr).2
  let : _root_.MeasureTheory.IsFiniteMeasure (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure (_root_.Set.Ioo a c)) := ⟨by
    rw [MeasureTheory.Measure.Subtype.volume_univ measurableSet_Ioo.nullMeasurableSet]
    exact measure_Ioo_lt_top⟩
  exact tendsto_integral_mul_of_uniform_abs_bound_div hF hb heta hetabound hradii

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_integral_mul_redDensity_limit_radialDistanceCutoff_flux

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness

end
