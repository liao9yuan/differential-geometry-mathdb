import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.Manifold

theorem locallyPathConnectedSpace_of_modelWithCorners
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] : LocallyPathConnectedSpace M := by
  have : LocallyPathConnectedSpace (_root_.Set.range I) := I.convex_range.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace H := I.isClosedEmbedding.isEmbedding.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ``Submission.DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners

end DifferentialGeometry.Topology.Manifold
