import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.ThreeManifold

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def isClosedThreeManifold : Prop :=
  CompactSpace M ∧ ConnectedSpace M ∧ I.Boundaryless ∧
    Module.finrank ℝ E = 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.isClosedThreeManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.isClosedThreeManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.isClosedThreeManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.isClosedThreeManifold

end DifferentialGeometry.Topology.ThreeManifold
