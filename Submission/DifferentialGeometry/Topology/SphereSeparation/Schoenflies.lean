import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Manifold
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.SphereSeparation

def smoothSchoenfliesThree : Prop :=
  ∀ e : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3),
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3)
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) ∞,
      _root_.Metric.closedBall 0 1 ⊆ Φ.source ∧ Φ '' _root_.Metric.sphere 0 1 = _root_.Set.range e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSchoenfliesThree

end DifferentialGeometry.Topology.SphereSeparation
