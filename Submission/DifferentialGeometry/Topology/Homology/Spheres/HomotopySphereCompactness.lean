import Submission.DifferentialGeometry.Topology.Homology.Local.Noncompact
import Submission.DifferentialGeometry.Topology.Homology.Spheres.CompactZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

open scoped _root_.Manifold _root_.ContDiff _root_.ContinuousMap
open _root_.Metric

theorem compactSpace_of_homotopyEquiv_sphere {n : ℕ} {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : CompactSpace M := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact SingularPair.compactSpace_of_homotopyEquiv_sphere_zero e
  · exact SingularPair.compactSpace_of_homotopyEquiv_sphere_of_one_le hn e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere ``Submission.DifferentialGeometry.Topology.compactSpace_of_homotopyEquiv_sphere

end DifferentialGeometry.Topology
