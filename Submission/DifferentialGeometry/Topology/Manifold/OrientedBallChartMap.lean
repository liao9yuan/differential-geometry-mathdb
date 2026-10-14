import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingIsometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.OrientedBallChart

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.OrientedBallChart.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.OrientedBallChart.E3 target :: scope.openDecls } }

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}

def map (c : OrientedBallChart M) (F : ClosedOrientedManifold.OrientedDiffeomorph M N) :
    OrientedBallChart N where
  chart := compPartialDiffeomorph c.chart F.val
  closedBall_subset_source := c.closedBall_subset_source
  preserves_orientation := preservesOrientation_compPartialDiffeomorph c.chart
    M.orientation N.orientation F.val F.property c.preserves_orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.map ``Submission.DifferentialGeometry.Topology.OrientedBallChart.map

theorem map_apply (c : OrientedBallChart M) (F : ClosedOrientedManifold.OrientedDiffeomorph M N) (x : E3) :
    (c.map F).chart x = F.val (c.chart x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.map_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.map_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.map_apply ``Submission.DifferentialGeometry.Topology.OrientedBallChart.map_apply

theorem disjoint_map_closedBall (c d : OrientedBallChart M)
    (F : ClosedOrientedManifold.OrientedDiffeomorph M N)
    (h : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)) :
    Disjoint ((c.map F).chart '' Metric.closedBall 0 2) ((d.map F).chart '' Metric.closedBall 0 2) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
  exact Set.disjoint_left.mp h ⟨x, hx, rfl⟩ ⟨z, hz, F.val.injective hzx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.OrientedBallChart.disjoint_map_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.OrientedBallChart.disjoint_map_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.OrientedBallChart.disjoint_map_closedBall ``Submission.DifferentialGeometry.Topology.OrientedBallChart.disjoint_map_closedBall

end DifferentialGeometry.Topology.OrientedBallChart
