import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointGeodesicSemiconcavity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMinimizerCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
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

namespace HalfLineMetricConvergenceData

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData renaming
  exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval →
    flow_semiconcavity in
theorem exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J : Set P.M} (hJ : IsCompact J) {δ T A B : ℝ}
    (hδ : 1 < δ)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ n : ℕ, ∀ k ≥ n, ∀ t ∈ _root_.Set.Icc δ T,
      ∀ (beta : ℝ → P.M) (a b : ℝ),
      (∀ r ∈ _root_.Set.Icc a b, IsGeodesicAt R beta r) → _root_.Set.MapsTo beta (_root_.Set.Icc a b) J →
      (∀ r ∈ _root_.Set.Icc a b, Real.sqrt (R.inner (beta r)
        (lVelocity (I := I) beta r) (lVelocity (I := I) beta r)) ≤ B) →
      ConcaveOn ℝ (_root_.Set.Icc a b)
        (fun r ↦ redLength ((U).term (phi (co.φ k))).S 0 p
          (Phi.map (co.φ k) (beta r)) t - D / 2 * r ^ 2) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨m, hm⟩ := exists_nat_gt T
  have hsub : _root_.Set.Icc (1 - T) (-(δ - 1) / 2) ⊆ _root_.Set.Icc (-(m : ℝ)) 0 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  let coW : FlowMetricConvergenceData Phi R bf hsrc htgt (1 - T) (-(δ - 1) / 2) :=
    FlowMetricConvergenceData.restrict Phi
      (HalfLineMetricConvergenceData.atWindow Phi co m) hsub
  have hG : MetricFamilySmoothOn (Y).D co.gInf :=
    HalfLineMetricConvergenceData.metricSmooth (Φ := Phi) co rfl (fun _ hx ↦ hx)
  obtain ⟨W, _hW, hcost⟩ :=
    exists_eventually_poleEndpoint_redLength_le_on_compact_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ
        (zero_lt_one.trans hδ) hbase
  obtain ⟨K, hK, hJK, hcapture⟩ :=
    exists_compact_eventual_poleEndpoint_minimizer_capture_of_basepoint_bound
      F hcar hreg b hbmem tau q hsigma Phi R hR co hcomplete kappa hF p hJ hδ hbase
  exact
    flow_semiconcavity
      F hcar hreg b hbmem tau q hsigma Phi R bf hsrc htgt hδ coW hG hboundary
      kappa hF p hK hJK (hcost.mono fun _ hk t ht y hy ↦ hk y hy t ht) hcapture

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
