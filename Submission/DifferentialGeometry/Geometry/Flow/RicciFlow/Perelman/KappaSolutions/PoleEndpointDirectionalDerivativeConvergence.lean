import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HalfLinePoleEndpointSemiconcavity
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.IntrinsicLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set _root_.Submission.Set _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Analysis.Calculus
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

theorem tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic
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
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : _root_.Filter.Tendsto rho _root_.Filter.atTop _root_.Filter.atTop)
    (lag : ℕ → ℝ) (hlag : ∀ᶠ k in _root_.Filter.atTop, lag k ∈ _root_.Set.Icc δ T)
    (beta : ℝ → P.M) {a c r : ℝ} (hr : r ∈ interior (_root_.Set.Icc a c))
    (hbeta : ∀ s ∈ _root_.Set.Icc a c, IsGeodesicAt R beta s)
    (hbetaJ : _root_.Set.MapsTo beta (_root_.Set.Icc a c) J)
    (hspeed : ∀ s ∈ _root_.Set.Icc a c, Real.sqrt (R.inner (beta s)
      (lVelocity (I := I) beta s) (lVelocity (I := I) beta s)) ≤ B)
    (f : P.M → ℝ)
    (hlim : ∀ s ∈ _root_.Set.Icc a c, _root_.Filter.Tendsto
      (fun k ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) (beta s)) (lag k)) _root_.Filter.atTop (𝓝 (f (beta s))))
    (hsourceDiff : ∀ᶠ k in _root_.Filter.atTop, MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) (lag k)) (beta r))
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (beta r)) :
    Tendsto (fun k ↦ mvfderiv (I := I)
        (fun y ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
          (Phi.map (co.φ (rho k)) y) (lag k)) (beta r) (lVelocity (I := I) beta r))
      atTop (𝓝 (mvfderiv (I := I) f (beta r) (lVelocity (I := I) beta r))) := by
  obtain ⟨D, _hD, n, hconcave⟩ :=
    exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
      kappa hF p hJ hδ hbase
  have hconcaveEv : ∀ᶠ k in _root_.Filter.atTop, ConcaveOn ℝ (_root_.Set.Icc a c)
      (fun s ↦ redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) (beta s)) (lag k) - D / 2 * s ^ 2) := by
    filter_upwards [hrho.eventually (_root_.Filter.eventually_ge_atTop n), hlag] with k hk ht
    exact hconcave (rho k) hk (lag k) ht beta a c hbeta hbetaJ hspeed
  have hbetaDiff : MDifferentiableAt 𝓘(ℝ, ℝ) I beta r :=
    (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt
      (hbeta r (interior_subset hr))).mdifferentiableAt (by simp)
  exact tendsto_mvfderiv_along_of_concaveOn_sub hr hbetaDiff hconcaveEv hsourceDiff hlim hf
    (by fun_prop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.tendsto_mvfderiv_poleEndpoint_redLength_along_of_geodesic

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
