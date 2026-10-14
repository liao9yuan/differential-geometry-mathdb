import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointUpperSupport
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostContinuity
import Submission.DifferentialGeometry.Analysis.Convex.CenteredUpperSupport

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

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

namespace FlowMetricConvergenceData

theorem exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval
    (Φ : PointedCGHMaps (I := I) Y P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {δ T : ℝ} (hδ : 1 < δ)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (1 - T) (-(δ - 1) / 2))
    (hG : MetricFamilySmoothOn (Y).D co.gInf)
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {J K : Set P.M} (hK : IsCompact K) (hJK : J ⊆ K)
    {B W : ℝ}
    (hcost : ∀ᶠ k in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc δ T, ∀ y ∈ J,
      @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
        (Φ.map (co.φ k) y) t ≤ W)
    (hcapture : ∀ᶠ k in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc δ T, ∀ y ∈ J,
      ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      @IsLRegularizedGeodesicOn E _ _ _ H _ I _ F.M F.topology F.charted F.smooth F.t2 _
        ((U).term (phi (co.φ k))).S 0 alpha (_root_.Set.Ioc 0 (Real.sqrt t)) →
      alpha 0 = p → alpha (Real.sqrt t) = Φ.map (co.φ k) y →
      @lRegularizedAction E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt t) =
        @lCost E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p (Φ.map (co.φ k) y) t →
      alpha '' _root_.Set.Icc (_root_.Max.max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt t / 2))
        (Real.sqrt t) ⊆ Φ.map (co.φ k) '' K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ n : ℕ, ∀ k ≥ n, ∀ t ∈ _root_.Set.Icc δ T, ∀ (beta : ℝ → P.M) (a b : ℝ),
      (∀ r ∈ _root_.Set.Icc a b, IsGeodesicAt R beta r) → _root_.Set.MapsTo beta (_root_.Set.Icc a b) J →
      (∀ r ∈ _root_.Set.Icc a b, Real.sqrt (R.inner (beta r)
        (lVelocity (I := I) beta r) (lVelocity (I := I) beta r)) ≤ B) →
      ConcaveOn ℝ (_root_.Set.Icc a b)
        (fun r ↦ @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
          (Φ.map (co.φ k) (beta r)) t - D / 2 * r ^ 2) := by
  obtain ⟨D, hD, n₁, hsupport⟩ :=
    exists_eventually_poleEndpoint_redLength_upper_support_on_time_interval_of_geodesic_capture
      F hcar hreg b hbmem tau q hsigma Φ R bf hsrc htgt hδ co hG hboundary
        kappa hF p hK hJK hcost hcapture
  obtain ⟨m, hm⟩ := Φ.source_subset hK
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp
    (co.strictMono.tendsto_atTop.eventually (_root_.Filter.eventually_ge_atTop m))
  refine ⟨D, hD, _root_.Max.max n₁ n₂, ?_⟩
  intro k hk t htau beta a b hbeta hbetaJ hspeed
  have hk₁ : n₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : n₂ ≤ k := (le_max_right _ _).trans hk
  have hsource : K ⊆ Φ.source (co.φ k) := hm (co.φ k) (hn₂ k hk₂)
  apply DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support
    (convex_Icc a b)
  · apply (continuous_redLength_of_ancient ((U).term (phi (co.φ k)))
      (hF (phi (co.φ k))) p ((zero_lt_one.trans hδ).trans_le htau.1)).comp_continuousOn
    intro r hr
    have hmap := (Φ.partialDiffeomorph (co.φ k)).isLocalDiffeomorphAt I I ∞
      (hsource (hJK (hbetaJ hr)))
    exact (hmap.contMDiffAt.continuousAt.comp (hbeta r hr).continuousAt).continuousWithinAt
  · intro x hx
    have hxi : x ∈ _root_.Set.Icc a b := interior_subset hx
    let gamma : ℝ → P.M := fun r ↦ beta (r + x)
    have hgamma : IsGeodesicAt R gamma 0 := by
      simpa only [sub_self] using
        DifferentialGeometry.Geometry.isGeodesicAt_comp_add (hbeta x hxi) x
    have hvel : lVelocity (I := I) gamma 0 = lVelocity (I := I) beta x := by
      have hdiff := (DifferentialGeometry.Geometry.contMDiffAt_of_isGeodesicAt
        (hbeta x hxi)).mdifferentiableAt (by simp)
      have hh := DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one
        (I := I) (γ := beta) 0 x (by simpa only [zero_add] using hdiff)
      unfold lVelocity
      rw [zero_add] at hh
      exact hh
    have hgammaSpeed : Real.sqrt (R.inner (gamma 0)
        (lVelocity (I := I) gamma 0) (lVelocity (I := I) gamma 0)) ≤ B := by
      rw [hvel]
      change Real.sqrt (R.inner (beta (0 + x))
        (lVelocity (I := I) beta x) (lVelocity (I := I) beta x)) ≤ B
      rw [zero_add]
      exact hspeed x hxi
    obtain ⟨ψ, hψ, htouch, hupper, hsecond⟩ := hsupport k hk₁ t htau gamma hgamma
      (by simpa only [gamma, zero_add] using hbetaJ hxi) hgammaSpeed
    refine ⟨ψ, hψ.contDiffAt, ?_, ?_, hsecond⟩
    · simpa only [gamma, zero_add] using htouch
    · filter_upwards [hupper] with r hr
      simpa only [gamma, add_comm] using hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_concaveOn_poleEndpoint_redLength_sub_quadratic_on_time_interval


end FlowMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
