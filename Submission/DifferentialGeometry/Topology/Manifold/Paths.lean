import Submission.DifferentialGeometry.Topology.Manifold.CountableAtlas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Homotopy.Lifting

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

include E in
theorem pathConnectedSpace_of_connected [ConnectedSpace M] : PathConnectedSpace M := by
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.pathConnectedSpace_of_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.pathConnectedSpace_of_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.pathConnectedSpace_of_connected ``Submission.DifferentialGeometry.Topology.Manifold.pathConnectedSpace_of_connected

theorem paths_homotopicRel [SimplyConnectedSpace M] {x y : M} (γ δ : Path x y) :
    γ.toContinuousMap.HomotopicRel δ.toContinuousMap {0, 1} :=
  SimplyConnectedSpace.paths_homotopic γ δ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.paths_homotopicRel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.paths_homotopicRel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.paths_homotopicRel ``Submission.DifferentialGeometry.Topology.Manifold.paths_homotopicRel

end DifferentialGeometry.Topology.Manifold
