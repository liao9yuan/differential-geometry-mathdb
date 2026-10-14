import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointUpperSupport
import Submission.DifferentialGeometry.Geometry.Geodesic.CompactChartUpperSupport

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
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instT2SpaceM_2 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.instSigmaCompactSpaceM_2 target :: scope.openDecls } }

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem times q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem times q hsigma

namespace FlowMetricConvergenceData

theorem
    exists_eventually_poleEndpoint_redLength_affine_upper_support_of_geodesic_capture_and_lipschitz
    (Φ : PointedCGHMaps (I := I) Y P phi)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {δ T : ℝ} (hδ : 1 < δ)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (1 - T) (-(δ - 1) / 2))
    (hG : MetricFamilySmoothOn (Y).D co.gInf)
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) (a : P.M) {J K : Set P.M}
    (hJ : IsCompact J) (hchart : J ⊆ (chartAt H a).source)
    (hK : IsCompact K) (hJK : J ⊆ K) {W : ℝ}
    (hcost : ∀ᶠ k in _root_.Filter.atTop, ∀ tau ∈ _root_.Set.Icc δ T, ∀ y ∈ J,
      @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p
        (Φ.map (co.φ k) y) tau ≤ W)
    (hcapture : ∀ᶠ k in _root_.Filter.atTop, ∀ tau ∈ _root_.Set.Icc δ T, ∀ y ∈ J, ∀ alpha : ℝ → F.M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      @IsLRegularizedGeodesicOn E _ _ _ H _ I _ F.M F.topology F.charted F.smooth F.t2 _
        ((U).term (phi (co.φ k))).S 0 alpha (_root_.Set.Ioc 0 (Real.sqrt tau)) →
      alpha 0 = p → alpha (Real.sqrt tau) = Φ.map (co.φ k) y →
      @lRegularizedAction E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 alpha 0 (Real.sqrt tau) =
        @lCost E _ _ _ H _ I F.M F.topology F.charted F.smooth _
        ((U).term (phi (co.φ k))).S 0 p (Φ.map (co.φ k) y) tau →
      alpha '' _root_.Set.Icc (_root_.Max.max (Real.sqrt ((1 + δ) / 2)) (Real.sqrt tau / 2))
        (Real.sqrt tau) ⊆ Φ.map (co.φ k) '' K)
    (L : ℝ≥0)
    (hLip : ∀ᶠ k in _root_.Filter.atTop, ∀ t ∈ _root_.Set.Icc δ T, ∀ y ∈ J, ∃ s : Set E,
      s ∈ 𝓝 (extChartAt I a y) ∧
      LipschitzOnWith L
        (fun v => @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
          ((U).term (phi (co.φ k))).S 0 p
          (Φ.map (co.φ k) ((extChartAt I a).symm v)) t) s) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ n : ℕ, ∀ k ≥ n, ∀ t ∈ _root_.Set.Icc δ T,
      ∀ y ∈ J, ∀ w : E, ∃ ψ : ℝ → ℝ, ContDiffAt ℝ 2 ψ 0 ∧
        ψ 0 = @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
          ((U).term (phi (co.φ k))).S 0 p (Φ.map (co.φ k) y) t ∧
        (fun r => @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
          ((U).term (phi (co.φ k))).S 0 p
          (Φ.map (co.φ k) ((extChartAt I a).symm (extChartAt I a y + r • w))) t)
          ≤ᶠ[𝓝 (0 : ℝ)] ψ ∧
        deriv (deriv ψ) 0 ≤ D * ‖w‖ ^ 2 := by
  obtain ⟨B, C, _, hC, hchartSupport⟩ :=
    exists_affine_chart_upper_support_bounds_of_geodesic_support_bounds R a hJ hchart
  obtain ⟨D₀, hD₀, n₁, hsupport⟩ :=
    exists_eventually_poleEndpoint_redLength_upper_support_on_time_interval_of_geodesic_capture
      F hcar hreg b hbmem times q hsigma Φ R bf hsrc htgt hδ co hG hboundary
      kappa hF p hK hJK (B := B) hcost hcapture
  obtain ⟨n₂, hLip₂⟩ := eventually_atTop.mp hLip
  refine ⟨D₀ + 2 * (L : ℝ) * (C + 1), by positivity, _root_.Max.max n₁ n₂, ?_⟩
  intro k hk t ht y hy w
  have hk₁ : n₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : n₂ ≤ k := (le_max_right _ _).trans hk
  let f : P.M → ℝ := fun z =>
    @redLength E _ _ _ H _ I F.M F.topology F.charted F.smooth _
      ((U).term (phi (co.φ k))).S 0 p (Φ.map (co.φ k) z) t
  have hsupp : ∀ γ : ℝ → P.M, IsGeodesicAt (I := I) R γ 0 → γ 0 ∈ J →
      Real.sqrt (R.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ≤ B →
      ∃ φ : ℝ → ℝ, ContDiffAt ℝ 2 φ 0 ∧ φ 0 = f (γ 0) ∧
        (fun r => f (γ r)) ≤ᶠ[𝓝 (0 : ℝ)] φ ∧ deriv (deriv φ) 0 ≤ D₀ := by
    intro γ hγ hγJ hspeed
    obtain ⟨φ, hφ, hzero, hupper, hsecond⟩ := hsupport k hk₁ t ht γ hγ hγJ hspeed
    exact ⟨φ, hφ.contDiffAt, hzero, hupper, hsecond⟩
  obtain ⟨s, hs, hfs⟩ := hLip₂ k hk₂ t ht y hy
  exact hchartSupport f L D₀ hsupp y hy s hs hfs w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_poleEndpoint_redLength_affine_upper_support_of_geodesic_capture_and_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_poleEndpoint_redLength_affine_upper_support_of_geodesic_capture_and_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_poleEndpoint_redLength_affine_upper_support_of_geodesic_capture_and_lipschitz ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricConvergenceData.exists_eventually_poleEndpoint_redLength_affine_upper_support_of_geodesic_capture_and_lipschitz

end FlowMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
