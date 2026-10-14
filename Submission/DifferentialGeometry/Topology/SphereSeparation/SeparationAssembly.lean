import Submission.DifferentialGeometry.Topology.SphereSeparation.OpenThreeSpace
import Submission.DifferentialGeometry.Topology.SphereSeparation.HalfSpaceClosure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def smoothSphereSidesOpenThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : HasAlexanderDualityH0Certificate (ψ ∘ e)) :
    SmoothSphereSides (Set.range e) := by
  let d := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
    e he ψ hAD
  exact {
    toSphereSides := d
    compactClosureSmooth := compactSmoothSideClosure he d
    endClosureSmooth := endSmoothSideClosure he d
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_alexanderDuality

theorem smoothSphereSides_side_sets_unique
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {S : Set N} (d₁ d₂ : SmoothSphereSides S) :
    d₁.compactSide = d₂.compactSide ∧ d₁.endSide = d₂.endSide :=
  SphereSides.side_sets_unique d₁.toSphereSides d₂.toSphereSides

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSides_side_sets_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSphereSides_side_sets_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSides_side_sets_unique ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSphereSides_side_sets_unique

end DifferentialGeometry.Topology.SphereSeparation
