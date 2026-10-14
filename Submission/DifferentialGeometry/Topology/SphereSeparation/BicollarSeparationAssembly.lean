import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarCertificates
import Submission.DifferentialGeometry.Topology.SphereSeparation.SeparationAssembly

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set _root_.Topology
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation

noncomputable def smoothSphereSidesOpenThreeSpace_of_openBicollar_of_sphereH1
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = ψ (e p))
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    SmoothSphereSides (Set.range e) :=
  smoothSphereSidesOpenThreeSpace_of_alexanderDuality e he ψ
    (hasAlexanderDualityH0Certificate_of_openBicollar_of_sphereH1
      ha (ψ ∘ e) Φ hΦ hzero hSphere)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar_of_sphereH1

noncomputable def smoothSphereSidesOpenThreeSpace_of_openBicollar
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    [IsManifold (modelWithCornersSelf ℝ EuclideanThree) ∞ N]
    (e : SphereTwo → N)
    (he : Manifold.IsSmoothEmbedding
      (𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, EuclideanThree)) ∞ e)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : _root_.Topology.IsOpenEmbedding Φ)
    (hzero : ∀ p, Φ (p, axialZero ha) = ψ (e p))
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    SmoothSphereSides (Set.range e) :=
  smoothSphereSidesOpenThreeSpace_of_alexanderDuality e he ψ
    (hasAlexanderDualityH0Certificate_of_openBicollar
      ha (ψ ∘ e) Φ hΦ hzero comparison)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar ``Submission.DifferentialGeometry.Topology.SphereSeparation.smoothSphereSidesOpenThreeSpace_of_openBicollar

theorem bicollar_sides_openThreeSpace_of_sphereH1
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1)) :
    let hAD :=
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere (axialZero ha)
    let d :=
      topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
        Φ hΦ ψ (axialZero ha) hAD
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  exact bicollar_sides_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ
      (hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere (axialZero ha))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_sphereH1

theorem bicollar_sides_openThreeSpace_of_cellularComparison
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex) :
    let hAD :=
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison (axialZero ha)
    let d :=
      topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
        Φ hΦ ψ (axialZero ha) hAD
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  exact bicollar_sides_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ
      (hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison (axialZero ha))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_cellularComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_cellularComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_cellularComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_cellularComparison

theorem bicollar_order_openThreeSpace_of_sphereH1
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hSphere : _root_.CategoryTheory.Limits.IsZero
      (integerSingularHomology (TopCat.of SphereTwo) 1))
    (o₀ :
      let hAD := fun c ↦
        hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
          (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere c
      IsAxiallyOrientedAtZero ha Φ
        (bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD))
    {s t : AxialInterval a} (hst : s < t) :
    let hAD := fun c ↦
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere c
    let d := bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  let _ : T2Space N := ψ.symm.toHomeomorph.t2Space
  let hAD := fun c ↦
    hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding_of_sphereH1
      (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) hSphere c
  exact bicollar_order_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ hAD o₀ hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_sphereH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_sphereH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_sphereH1 ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_sphereH1

theorem bicollar_order_openThreeSpace_of_cellularComparison
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (comparison : HomotopyEquiv
      (integerSingularChains (TopCat.of SphereTwo))
      sphereTwoCellularChainComplex)
    (o₀ :
      let hAD := fun c ↦
        hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
          (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison c
      IsAxiallyOrientedAtZero ha Φ
        (bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD))
    {s t : AxialInterval a} (hst : s < t) :
    let hAD := fun c ↦
      hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
        (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison c
    let d := bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD
    (closure (d s).compactSide ⊆ (d t).compactSide ∧
      (d t).compactSide = interior (closure (d t).compactSide)) ∧
    closure (d t).compactSide =
      closure (d s).compactSide ∪ closedSlabImage Φ s t ∧
    ((closedSlabImage Φ s t)ᶜ =
        (d s).compactSide ∪ (d t).endSide ∧
      Disjoint (d s).compactSide (d t).endSide) ∧
    closure (d s).compactSide ⊂ (d t).compactSide ∧
    closure (d s).compactSide ⊂ closure (d t).compactSide := by
  let _ : T2Space N := ψ.symm.toHomeomorph.t2Space
  let hAD := fun c ↦
    hasAlexanderDualityH0Certificate_bicollarSlice_of_smoothEmbedding
      (ψ ∘ Φ) (hΦ.postcomp_diffeomorph ψ) comparison c
  exact bicollar_order_openThreeSpace_of_alexanderDuality
    ha Φ hΦ ψ hAD o₀ hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_cellularComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_cellularComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_cellularComparison ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_cellularComparison

end DifferentialGeometry.Topology.SphereSeparation
