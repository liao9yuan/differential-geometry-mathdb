import Submission.DifferentialGeometry.Topology.SphereSeparation.Nesting
import Submission.DifferentialGeometry.Topology.SphereSeparation.OpenThreeSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

theorem disjoint_spheres_nested_openThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e₁ e₂ : SphereTwo → N)
    (he₁ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₂)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD₁ : HasAlexanderDualityH0Certificate (ψ ∘ e₁))
    (hAD₂ : HasAlexanderDualityH0Certificate (ψ ∘ e₂))
    (hdisjoint : Disjoint (Set.range e₁) (Set.range e₂))
    (hmeet :
      let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
        e₁ he₁ ψ hAD₁
      let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
        e₂ he₂ ψ hAD₂
      (d₁.compactSide ∩ d₂.compactSide).Nonempty) :
    let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
      e₁ he₁ ψ hAD₁
    let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
      e₂ he₂ ψ hAD₂
    Xor
      (closure d₁.compactSide ⊂ d₂.compactSide ∧
        d₂.compactSide = interior (closure d₂.compactSide) ∧
        closure d₁.compactSide ⊂ closure d₂.compactSide)
      (closure d₂.compactSide ⊂ d₁.compactSide ∧
        d₁.compactSide = interior (closure d₁.compactSide) ∧
        closure d₂.compactSide ⊂ closure d₁.compactSide) := by
  let d₁ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
    e₁ he₁ ψ hAD₁
  let d₂ := topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
    e₂ he₂ ψ hAD₂
  exact d₁.disjoint_sides_strictly_nested d₂ hdisjoint
    (isConnected_range he₁.contMDiff.continuous)
    (isConnected_range he₂.contMDiff.continuous) hmeet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace_of_alexanderDuality

end DifferentialGeometry.Topology.SphereSeparation
