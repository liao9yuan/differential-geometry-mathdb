import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import Submission.DifferentialGeometry.Geometry.Curvature.Nonnegative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.NNReal

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_radius_busemann_ray_gt (g : SmoothRiemannianMetric I M)
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g)
    (hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g)
    (p : M) (A : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : M, R < _root_.Dist.dist p x →
      ∃ c : ℝ≥0 → M, Isometry c ∧ c 0 = p ∧ A < busemann c x := by
  obtain ⟨R, hR, hbound⟩ :=
    (isCompact_rayBusemannSublevel g hEnorm hsec p A).isBounded.subset_closedBall_lt 0 p
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hnot : x ∉ rayBusemannSublevel p A := by
    intro hmem
    have hdist := hbound hmem
    rw [Metric.mem_closedBall, dist_comm] at hdist
    exact hx.not_ge hdist
  change ¬ (∀ c : ℝ≥0 → M, Isometry c → c 0 = p → busemann c x ≤ A) at hnot
  push Not at hnot
  exact hnot

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_radius_busemann_ray_gt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_radius_busemann_ray_gt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_radius_busemann_ray_gt ``Submission.DifferentialGeometry.Geometry.Topology.exists_radius_busemann_ray_gt

end DifferentialGeometry.Geometry.Topology
