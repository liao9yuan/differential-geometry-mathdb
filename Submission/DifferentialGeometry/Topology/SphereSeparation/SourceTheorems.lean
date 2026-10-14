import Submission.DifferentialGeometry.Topology.SphereSeparation.GlobalBicollarAssembly
import Submission.DifferentialGeometry.Topology.SphereSeparation.RadialExtensionDerivative
import Submission.DifferentialGeometry.Topology.SphereSeparation.SphereH1

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

theorem embeddedSphere_hasAlexanderDualityH0Certificate
    (e : SphereTwo → EuclideanThree)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ EuclideanThree) ∞ e) :
    HasAlexanderDualityH0Certificate e :=
  hasAlexanderDualityH0Certificate_of_smooth_normalField_of_sphereH1
    he (contMDiff_embeddedSphereAdjugateNormal he)
    (fun p ↦ (embeddedSphereAdjugateNormal_ne_zero_mem he p).2)
    (fun p ↦ (embeddedSphereAdjugateNormal_ne_zero_mem he p).1)
    isZero_integerSingularHomology_sphereTwo_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_hasAlexanderDualityH0Certificate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_hasAlexanderDualityH0Certificate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_hasAlexanderDualityH0Certificate ``Submission.DifferentialGeometry.Topology.SphereSeparation.embeddedSphere_hasAlexanderDualityH0Certificate

noncomputable def jordanBrouwer_openThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞) :
    SmoothSphereSides (Set.range e) :=
  smoothSphereSidesOpenThreeSpace_of_alexanderDuality e he ψ
    (embeddedSphere_hasAlexanderDualityH0Certificate
      (ψ ∘ e) (he.postcomp_diffeomorph ψ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace


noncomputable def compactSideOpenThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞) : Set N :=
  (jordanBrouwer_openThreeSpace e he ψ).compactSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.compactSideOpenThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.compactSideOpenThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.compactSideOpenThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.compactSideOpenThreeSpace


noncomputable def endSideOpenThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞) : Set N :=
  (jordanBrouwer_openThreeSpace e he ψ).endSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.endSideOpenThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.endSideOpenThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.endSideOpenThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.endSideOpenThreeSpace

theorem jordanBrouwer_openThreeSpace_unique
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (B E : Set N) (hBopen : IsOpen B) (hEopen : IsOpen E)
    (hBconnected : IsConnected B) (hEconnected : IsConnected E)
    (hdisjoint : Disjoint B E)
    (hunion : B ∪ E = (Set.range e)ᶜ)
    (hBcompact : IsCompact (closure B))
    (hEnoncompact : ¬ IsCompact (closure E)) :
    B = compactSideOpenThreeSpace e he ψ ∧
      E = endSideOpenThreeSpace e he ψ := by
  exact SphereSides.side_sets_unique_of_core_properties
    (jordanBrouwer_openThreeSpace e he ψ).toSphereSides B E
    hBopen hEopen hBconnected hEconnected hdisjoint hunion
    hBcompact hEnoncompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_unique ``Submission.DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_unique

noncomputable def jordanBrouwer_openThreeSpace_components
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞) :
    ConnectedComponents (((Set.range e)ᶜ : Set N)) ≃ Fin 2 :=
  connectedComponentsComplEquivFinTwo
    (jordanBrouwer_openThreeSpace e he ψ).toSphereSides

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_components then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_components"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_components ``Submission.DifferentialGeometry.Topology.SphereSeparation.jordanBrouwer_openThreeSpace_components

noncomputable def bicollarSliceSidesOpenThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (c : AxialInterval a) : SphereSides (sliceImage Φ c) :=
  bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ
    (fun t ↦
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ)
        isZero_integerSingularHomology_sphereTwo_one t)
    c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace

theorem bicollar_sides_openThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞) :
    let d := bicollarSliceSidesOpenThreeSpace Φ hΦ ψ (axialZero ha)
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  simpa only [bicollarSliceSidesOpenThreeSpace,
    bicollarSliceSidesOpenThreeSpace_of_alexanderDuality] using
    bicollar_sides_openThreeSpace_of_sphereH1
      ha Φ hΦ ψ isZero_integerSingularHomology_sphereTwo_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace

theorem bicollar_order_openThreeSpace
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (o₀ :
      IsAxiallyOrientedAtZero ha Φ
        (bicollarSliceSidesOpenThreeSpace Φ hΦ ψ))
    {s t : AxialInterval a} (hst : s < t) :
    let d := bicollarSliceSidesOpenThreeSpace Φ hΦ ψ
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  simpa only [bicollarSliceSidesOpenThreeSpace,
    bicollarSliceSidesOpenThreeSpace_of_alexanderDuality] using
    bicollar_order_openThreeSpace_of_sphereH1
      ha Φ hΦ ψ isZero_integerSingularHomology_sphereTwo_one o₀ hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace

theorem disjoint_spheres_nested_openThreeSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e₁ e₂ : SphereTwo → N)
    (he₁ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₁)
    (he₂ : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e₂)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hdisjoint : Disjoint (Set.range e₁) (Set.range e₂))
    (hmeet :
      let d₁ := (jordanBrouwer_openThreeSpace e₁ he₁ ψ).toSphereSides
      let d₂ := (jordanBrouwer_openThreeSpace e₂ he₂ ψ).toSphereSides
      (d₁.compactSide ∩ d₂.compactSide).Nonempty) :
    let d₁ := (jordanBrouwer_openThreeSpace e₁ he₁ ψ).toSphereSides
    let d₂ := (jordanBrouwer_openThreeSpace e₂ he₂ ψ).toSphereSides
    Xor
      (closure d₁.compactSide ⊂ d₂.compactSide ∧
        d₂.compactSide = interior (closure d₂.compactSide) ∧
        closure d₁.compactSide ⊂ closure d₂.compactSide)
      (closure d₂.compactSide ⊂ d₁.compactSide ∧
        d₁.compactSide = interior (closure d₁.compactSide) ∧
        closure d₂.compactSide ⊂ closure d₁.compactSide) := by
  let d₁ := (jordanBrouwer_openThreeSpace e₁ he₁ ψ).toSphereSides
  let d₂ := (jordanBrouwer_openThreeSpace e₂ he₂ ψ).toSphereSides
  exact d₁.disjoint_sides_strictly_nested d₂ hdisjoint
    (isConnected_range he₁.contMDiff.continuous)
    (isConnected_range he₂.contMDiff.continuous) hmeet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace ``Submission.DifferentialGeometry.Topology.SphereSeparation.disjoint_spheres_nested_openThreeSpace

end DifferentialGeometry.Topology.SphereSeparation
