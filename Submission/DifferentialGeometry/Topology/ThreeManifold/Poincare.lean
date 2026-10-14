import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise352Producer
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Skeleton.PoincareEndgame

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem poincare_conjecture
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [CompactSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨C, hC⟩ := PiecewiseLinear.exists_isManifold_three (M := M)
  let := C
  let : IsManifold (𝓡 3) ∞ M := hC
  obtain ⟨f⟩ := PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds M
  exact ⟨f.toHomeomorph⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincare_conjecture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincare_conjecture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincare_conjecture ``Submission.DifferentialGeometry.Topology.poincare_conjecture

end DifferentialGeometry.Topology
