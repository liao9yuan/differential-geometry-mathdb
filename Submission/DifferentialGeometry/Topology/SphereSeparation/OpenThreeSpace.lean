import Submission.DifferentialGeometry.Topology.SphereSeparation.EuclideanComponents
import Submission.DifferentialGeometry.Topology.SphereSeparation.JordanBrouwer
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Topology.SphereSeparation.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem range_equiv_comp
    {X Y Z : Type*} (h : Y ≃ Z) (f : X → Y) :
    Set.range (h ∘ f) = h '' Set.range f := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_equiv_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SphereSeparation.range_equiv_comp target :: scope.openDecls } }

noncomputable def topologicalSphereSidesOpenThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hcount : HasTwoComplementComponents (ψ ∘ e))
    (happroach :
      let p := complementPairOfComponentCount
        ((isCompact_range
          (ψ.continuous.comp he.contMDiff.continuous)).isClosed.isOpen_compl)
        hcount
      Set.range (ψ ∘ e) ⊆ closure p.left ∧
        Set.range (ψ ∘ e) ⊆ closure p.right) :
    SphereSides (Set.range e) := by
  have hcompact : IsCompact (Set.range (ψ ∘ e)) :=
    isCompact_range (ψ.continuous.comp he.contMDiff.continuous)
  let p : ComplementPair (Set.range (ψ ∘ e)) :=
    complementPairOfComponentCount hcompact.isClosed.isOpen_compl hcount
  let dℝ : SphereSides (Set.range (ψ ∘ e)) :=
    sphereSidesOfComplementPair hcompact p happroach.1 happroach.2
  have hrange : Set.range (ψ ∘ e) = ψ '' Set.range e :=
    range_equiv_comp ψ.toEquiv e
  have hback : ψ.symm '' Set.range (ψ ∘ e) = Set.range e := by
    rw [hrange]
    rw [Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace

noncomputable def topologicalSphereSidesOpenThreeSpace_of_locallyTwoSided
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (𝓘(ℝ, EuclideanThree)) ∞ EuclideanThree]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hcount : HasTwoComplementComponents (ψ ∘ e))
    (hlocal : LocallyTwoSided (Set.range (ψ ∘ e))) :
    SphereSides (Set.range e) := by
  have heℝ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞
      (ψ ∘ e) :=
    he.postcomp_diffeomorph ψ
  let dℝ : SphereSides (Set.range (ψ ∘ e)) :=
    topologicalSphereSidesOfComponentCount_of_locallyTwoSided
      (ψ ∘ e) heℝ hcount hlocal
  have hrange : Set.range (ψ ∘ e) = ψ '' Set.range e :=
    range_equiv_comp ψ.toEquiv e
  have hback : ψ.symm '' Set.range (ψ ∘ e) = Set.range e := by
    rw [hrange, Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_locallyTwoSided then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_locallyTwoSided"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_locallyTwoSided ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_locallyTwoSided

noncomputable def topologicalSphereSidesOpenThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : HasAlexanderDualityH0Certificate (ψ ∘ e)) :
    SphereSides (Set.range e) := by
  have heℝ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞
      (ψ ∘ e) :=
    he.postcomp_diffeomorph ψ
  let dℝ : SphereSides (Set.range (ψ ∘ e)) :=
    topologicalSphereSidesOfAlexanderDuality (ψ ∘ e) heℝ hAD
  have hrange : Set.range (ψ ∘ e) = ψ '' Set.range e :=
    range_equiv_comp ψ.toEquiv e
  have hback : ψ.symm '' Set.range (ψ ∘ e) = Set.range e := by
    rw [hrange, Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_of_alexanderDuality

theorem topologicalSphereSidesOpenThreeSpace_unique
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hcount : HasTwoComplementComponents (ψ ∘ e))
    (happroach :
      let p := complementPairOfComponentCount
        ((isCompact_range
          (ψ.continuous.comp he.contMDiff.continuous)).isClosed.isOpen_compl)
        hcount
      Set.range (ψ ∘ e) ⊆ closure p.left ∧
        Set.range (ψ ∘ e) ⊆ closure p.right)
    (d : SphereSides (Set.range e)) :
    d = topologicalSphereSidesOpenThreeSpace e he ψ hcount happroach :=
  SphereSides.unique _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_unique ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_unique

end DifferentialGeometry.Topology.SphereSeparation
