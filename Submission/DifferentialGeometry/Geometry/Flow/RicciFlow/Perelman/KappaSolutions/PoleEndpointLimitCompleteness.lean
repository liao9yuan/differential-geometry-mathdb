import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

private theorem metric_zero_le_of_curvatureOperator_nonnegative
    (L : PointedFlowData (I := I) ancientTimeInterval)
    (hcurv : ∀ s ∈ ancientTimeInterval.carrier,
      PointedFlowNonnegativeCurvatureOperator L s)
    {s : ℝ} (hs : s ≤ 0) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    ∀ (x : L.M) (v : TangentSpace I x),
      (L.S.base.metric 0).inner x v v ≤ (L.S.base.metric s).inner x v v := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  intro x v
  have hRic : ∀ t ∈ _root_.Set.Ioo s 0, ∀ y : L.M, ∀ w : TangentSpace I y,
      0 ≤ L.S.ricciAt t y (vec2 w w) := by
    intro t ht y w
    apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
    apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
      (I := I) (L.S.base.metric t) y).mpr
    intro n c v' w'
    simpa [SolutionFamily.rm04, metricRm04StandardAt_apply, vec4] using
      hcurv t ht.2.le y n c v' w'
  have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior L.S L.isSolution
    (a := s) (b := 0) (fun _ ht => ht.2) (fun _ ht => ht.2) hRic x v
  exact hanti ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.metric_zero_le_of_curvatureOperator_nonnegative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.metric_zero_le_of_curvatureOperator_nonnegative target :: scope.openDecls } }

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
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

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

namespace HalfLineMetricConvergenceData

theorem metric_zero_le_poleEndpoint_limit_of_ancient
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {kappa : ℝ} (hAncient : IsAncientKappaSolution kappa F)
    {s : ℝ} (hs : s ≤ 0) (x : P.M) (v : TangentSpace I x) :
    (co.gInf 0).inner x v v ≤ (co.gInf s).inner x v v := by
  have hconv := co.metric_convergence (Φ := Phi) (fun _ ht => ht)
  have h0 := hconv 0 (by change (0 : ℝ) ≤ 0; exact le_rfl) x v v
  have htime := hconv s hs x v v
  apply le_of_tendsto_of_tendsto h0 htime
  filter_upwards [] with k
  simp only [Function.comp_apply, PointedCGHMaps.compSubseq_map]
  exact metric_zero_le_of_curvatureOperator_nonnegative ((Y).term (phi (co.φ k)))
    (fun t ht => poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator
      F hcar hreg b hbmem tau q hsigma hAncient.nonnegativeCurvatureOperator
        (phi (co.φ k)) ht) hs _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_zero_le_poleEndpoint_limit_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_zero_le_poleEndpoint_limit_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_zero_le_poleEndpoint_limit_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_zero_le_poleEndpoint_limit_of_ancient

theorem metric_complete_poleEndpoint_limit_of_ancient
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {kappa : ℝ} (hAncient : IsAncientKappaSolution kappa F)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    {s : ℝ} (hs : s ≤ 0) :
    MetricComplete ({ P with metric := co.gInf s } : PointedRiemannianManifold I) := by
  apply MetricComplete.complete_of_lower
    ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I)
    hcomplete (co.gInf s) 1 zero_lt_one
  intro x v
  simpa only [one_mul] using metric_zero_le_poleEndpoint_limit_of_ancient
    F hcar hreg b hbmem tau q hsigma Phi R co hAncient hs x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_of_ancient

theorem metric_complete_poleEndpoint_limit_time_sub_of_ancient
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {kappa : ℝ} (hAncient : IsAncientKappaSolution kappa F)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    {t : ℝ} (ht : 1 ≤ t) :
    MetricComplete ({ P with metric := co.gInf (1 - t) } : PointedRiemannianManifold I) :=
  metric_complete_poleEndpoint_limit_of_ancient F hcar hreg b hbmem tau q hsigma
    Phi R co hAncient hcomplete (sub_nonpos.mpr ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_time_sub_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_time_sub_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_time_sub_of_ancient ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_complete_poleEndpoint_limit_time_sub_of_ancient

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
