import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointChartSemiconcavity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointJointLipschitz
import Submission.DifferentialGeometry.Topology.LipschitzSwap
import Mathlib.Analysis.InnerProductSpace.LinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.TopologicalSpace
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
  (b : ℝ) (hbmem : b ∈ D.carrier) (times : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < times i + b)
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

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem times q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem times q hsigma

namespace HalfLineMetricConvergenceData

theorem exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) (a : P.M) {J : Set P.M} (hJ : IsCompact J)
    (hchart : J ⊆ (chartAt H a).source) {δ T A : ℝ} (hδ : 1 < δ)
    (hbase : ∀ᶠ k in _root_.Filter.atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    {W : Set E} (hWconv : Convex ℝ W) (hWJ : W ⊆ (extChartAt I a) '' J)
    {S : Set ℝ} (hST : S ⊆ _root_.Set.Icc δ T) :
    ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∀ᶠ k in _root_.Filter.atTop,
      let f : ℝ × E → ℝ := fun z => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) ((extChartAt I a).symm z.2)) z.1
      LocallyLipschitzOn (S ×ˢ W) f ∧
        ∀ t ∈ S, ConcaveOn ℝ W (fun z => f (t, z) - B z z / 2) := by
  have hWt : W ⊆ (extChartAt I a).target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWJ hz
    exact (extChartAt I a).map_source (by simpa only [extChartAt_source] using hchart hy)
  have hWInv : _root_.Set.MapsTo (extChartAt I a).symm W J := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hWJ hz
    rw [(extChartAt I a).left_inv (by simpa only [extChartAt_source] using hchart hy)]
    exact hy
  obtain ⟨D₀, _, n, hconcave⟩ :=
    exists_eventually_concaveOn_poleEndpoint_redLength_on_convex_chart_subset_sub_norm_sq
      F hcar hreg b hbmem times q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p a hJ hchart (T := T) hδ hbase
  let B : E →L[ℝ] E →L[ℝ] ℝ := D₀ • innerSL ℝ
  have hB (z : E) : B z z = D₀ * ‖z‖ ^ 2 := by
    change D₀ * _root_.Inner.inner ℝ z z = D₀ * ‖z‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  refine ⟨B, ?_⟩
  have hLip := eventually_locallyLipschitzOn_poleEndpoint_redLength_chart
    F hcar hreg b hbmem times q hsigma Phi R hR co kappa hF p hJ (c := T) hδ.le hbase a hWt hWInv
  filter_upwards [hrho.eventually hLip, hrho.eventually (_root_.Filter.eventually_ge_atTop n)] with k hk hn
  dsimp only
  constructor
  · exact hk.comp_swap.mono (Set.prod_mono hST Subset.rfl)
  · intro t ht
    apply (hconcave (rho k) hn t (hST ht) W hWconv hWJ).congr
    intro z _
    change _ - D₀ / 2 * ‖z‖ ^ 2 = _ - B z z / 2
    erw [hB]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_eventually_locallyLipschitzOn_concaveOn_poleEndpoint_redLength_chart

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
