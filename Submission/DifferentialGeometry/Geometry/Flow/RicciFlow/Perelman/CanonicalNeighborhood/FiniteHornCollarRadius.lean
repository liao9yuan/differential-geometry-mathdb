import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

private theorem radius_le_endpoint_dist_of_isCompact_closedBall
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (x : W) {R : ℝ}
    (hK : IsCompact (Metric.closedBall x R)) :
    R ≤ _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint := by
  by_contra hnot
  have hR : _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint < R := lt_of_not_ge hnot
  have hgap : 0 < R - _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint := sub_pos.mpr hR
  have hclosed : IsClosed ((fun y : W => (y : UniformSpace.Completion W)) '' Metric.closedBall x R) :=
    (hK.image (UniformSpace.Completion.continuous_coe W)).isClosed
  have he : H.endpoint ∈ closure
      ((fun y : W => (y : UniformSpace.Completion W)) '' Metric.closedBall x R) := by
    apply Metric.mem_closure_iff.mpr
    intro eta heta
    obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := W)).exists_dist_lt
      H.endpoint (lt_min heta hgap)
    have hygap : _root_.Dist.dist (y : UniformSpace.Completion W) H.endpoint <
        R - _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint := by
      rw [dist_comm]
      exact hy.trans_le (min_le_right _ _)
    have hyball : y ∈ Metric.closedBall x R := by
      change _root_.Dist.dist y x ≤ R
      have htri := dist_triangle (y : UniformSpace.Completion W) H.endpoint
        (x : UniformSpace.Completion W)
      rw [UniformSpace.Completion.dist_eq, dist_comm H.endpoint] at htri
      linarith
    exact ⟨(y : UniformSpace.Completion W), ⟨y, hyball, rfl⟩,
      hy.trans_le (min_le_left _ _)⟩
  rw [hclosed.closure_eq] at he
  obtain ⟨y, _hy, heq⟩ := he
  exact H.endpoint_missing y heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radius_le_endpoint_dist_of_isCompact_closedBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.radius_le_endpoint_dist_of_isCompact_closedBall target :: scope.openDecls } }

theorem collar_endpoint_distance_lower_bound
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    {Q : ℝ} (hQ : 0 < Q) (C : CylinderReference)
    (F : PartialDiffeomorph IC I3 Cylinder W ∞)
    {U : Set Cylinder} {times : Set ℝ} {order : ℕ} {eps R : ℝ}
    (cmp : MetricComparisonOn (fun _ => C.metric 0)
      (fun _ => scaleMetric Q hQ g) F U times order eps)
    (heps : eps ≤ 1 / 2) (hzero : 0 ∈ times) (hR : 0 < R)
    (hsource : U ⊆ F.source) (hslab : _root_.Set.univ ×ˢ _root_.Set.Icc (-R) R ⊆ U)
    (p : Sphere 2) :
    R / 4 ≤ Real.sqrt Q * _root_.Dist.dist (F (p, 0) : UniformSpace.Completion W) H.endpoint := by
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hcompact := collar_isCompact_closedBall C (fun _ => scaleMetric Q hQ g) F
    cmp rfl heps hzero hR (r := R / 4) (by linarith) hsource hslab p
  have hset : Metric.closedBall (F (p, 0)) (R / 4 / Real.sqrt Q) =
      riemannianClosedBallOf (scaleMetric Q hQ g) (F (p, 0)) (R / 4) := by
    ext y
    change _root_.Dist.dist y (F (p, 0)) ≤ R / 4 / Real.sqrt Q ↔
      riemannianEDistOf (scaleMetric Q hQ g) (F (p, 0)) y ≤ ENNReal.ofReal (R / 4)
    rw [edistOf_scale, H.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_mul hsqrt.le, ENNReal.ofReal_le_ofReal_iff (by positivity),
      le_div_iff₀ hsqrt, dist_comm y (F (p, 0)), mul_comm (_root_.Dist.dist (F (p, 0)) y)]
  have hactual : IsCompact (Metric.closedBall (F (p, 0)) (R / 4 / Real.sqrt Q)) := by
    rw [hset]
    exact hcompact
  have hdist := radius_le_endpoint_dist_of_isCompact_closedBall g H (F (p, 0)) hactual
  simpa only [mul_comm] using (div_le_iff₀ hsqrt).mp hdist

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_endpoint_distance_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_endpoint_distance_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_endpoint_distance_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.collar_endpoint_distance_lower_bound

theorem finiteHorn_scalar_radius_lower_bound
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ i, ∀ x ∈ H.subend i,
      H.collar_depth ^ 2 / 16 ≤
        metricScalarAt g x * _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint ^ 2 := by
  obtain ⟨i, htail⟩ := H.cylindrical_tail
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨C, F, p, hcenter, _hsection, hsource, hQ, ⟨cmp⟩⟩ := htail x hx
  have hbound := collar_endpoint_distance_lower_bound g H hQ C F cmp
    (by linarith [H.neck_precision_small]) (by simp) H.collar_depth_pos
    hsource (fun _ hy => hy) p
  rw [hcenter] at hbound
  have hnonneg : 0 ≤ Real.sqrt (metricScalarAt g x) *
      dist (x : UniformSpace.Completion W) H.endpoint + H.collar_depth / 4 := by
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) dist_nonneg)
      (div_nonneg H.collar_depth_pos.le (by norm_num))
  have hsq : (H.collar_depth / 4) ^ 2 ≤
      (Real.sqrt (metricScalarAt g x) * _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbound) hnonneg]
  rw [mul_pow, Real.sq_sqrt hQ.le] at hsq
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_scalar_radius_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_scalar_radius_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_scalar_radius_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_scalar_radius_lower_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
