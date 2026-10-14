import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.MetricSpace.ProperSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set _root_.Metric
open scoped _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

theorem exists_extChartAt_symm_image_closedBall_subset
    {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    [TopologicalSpace M] [ChartedSpace H M]
    (a : M) {W : Set E} {z : E} (hW : W ∈ 𝓝 z)
    (hWt : W ⊆ (extChartAt I a).target) :
    ∃ r : ℝ, 0 < r ∧ _root_.Metric.closedBall z r ⊆ W ∧
      IsCompact ((extChartAt I a).symm '' _root_.Metric.closedBall z r) ∧
      (extChartAt I a).symm '' _root_.Metric.closedBall z r ⊆ (extChartAt I a).source ∧
      ball z r ⊆ extChartAt I a '' ((extChartAt I a).symm '' _root_.Metric.closedBall z r) := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hW
  have htarget : _root_.Metric.closedBall z r ⊆ (extChartAt I a).target := hsub.trans hWt
  refine ⟨r, hr, hsub, ?_, ?_, ?_⟩
  · exact (_root_.ProperSpace.isCompact_closedBall z r).image_of_continuousOn
      ((continuousOn_extChartAt_symm a).mono htarget)
  · rintro x ⟨y, hy, rfl⟩
    exact (extChartAt I a).map_target (htarget hy)
  · rw [(extChartAt I a).image_symm_image_of_subset_target htarget]
    exact _root_.Metric.ball_subset_closedBall

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_extChartAt_symm_image_closedBall_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_extChartAt_symm_image_closedBall_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_extChartAt_symm_image_closedBall_subset ``Submission.DifferentialGeometry.Topology.Manifold.exists_extChartAt_symm_image_closedBall_subset

end DifferentialGeometry.Topology.Manifold
