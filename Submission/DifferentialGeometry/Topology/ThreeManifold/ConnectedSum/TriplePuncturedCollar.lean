import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TriplePunctured

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.BallChart

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.BallChart.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.BallChart.S2 target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] (e c d : BallChart 3 (𝓡 3) M)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))

def tripleRadialFirst (z : S2) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) : e.TriplePunctured c d := by
  have hmem : e.chart (r • z.val) ∈ e.chart '' Metric.closedBall 0 2 :=
    ⟨r • z.val, by rw [Metric.mem_closedBall, dist_zero_right, norm_radial z (by linarith [hr.1])]; exact hr.2, rfl⟩
  exact ⟨e.chart (r • z.val), (e.radialMap z r hr).property,
    fun h => Set.disjoint_left.mp hec hmem (Set.image_mono
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))) h),
    fun h => Set.disjoint_left.mp hed hmem (Set.image_mono
      (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2))) h)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleRadialFirst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleRadialFirst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleRadialFirst ``Submission.DifferentialGeometry.Topology.BallChart.tripleRadialFirst

theorem tripleRadialFirst_val (z : S2) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    (tripleRadialFirst e c d hec hed z r hr).val = e.chart (r • z.val) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleRadialFirst_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleRadialFirst_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleRadialFirst_val ``Submission.DifferentialGeometry.Topology.BallChart.tripleRadialFirst_val

theorem tripleToFirst_tripleRadialFirst (z : S2) (r : ℝ) (hr : r ∈ _root_.Set.Icc 1 2) :
    tripleToFirst e c d (tripleRadialFirst e c d hec hed z r hr) = e.radialMap z r hr := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.BallChart.tripleToFirst_tripleRadialFirst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.BallChart.tripleToFirst_tripleRadialFirst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.BallChart.tripleToFirst_tripleRadialFirst ``Submission.DifferentialGeometry.Topology.BallChart.tripleToFirst_tripleRadialFirst

end DifferentialGeometry.Topology.BallChart
