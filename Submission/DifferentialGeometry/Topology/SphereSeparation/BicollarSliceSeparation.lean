import Submission.DifferentialGeometry.Topology.SphereSeparation.BicollarLocalTwoSided
import Submission.DifferentialGeometry.Topology.SphereSeparation.JordanBrouwer
import Submission.DifferentialGeometry.Topology.SphereSeparation.SmoothEmbeddingComposition
import Submission.DifferentialGeometry.Topology.SphereSeparation.Transport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Function _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology.SphereSeparation


def bicollarSliceMap {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    SphereTwo → N :=
  fun x => Φ (x, c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollarSliceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollarSliceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollarSliceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollarSliceMap

theorem range_bicollarSliceMap {N : Type*} {a : ℝ}
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    Set.range (bicollarSliceMap Φ c) = sliceImage Φ c := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(x, c), ⟨Set.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    have hpEq : p = (p.1, c) := by
      apply Prod.ext
      · rfl
      · exact hp.2
    exact ⟨p.1, by rw [bicollarSliceMap, ← hpEq]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.range_bicollarSliceMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.range_bicollarSliceMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.range_bicollarSliceMap ``Submission.DifferentialGeometry.Topology.SphereSeparation.range_bicollarSliceMap

noncomputable def topologicalSphereSides_bicollarSlice_of_alexanderDuality
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → EuclideanThree)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (c : AxialInterval a)
    (hAD : HasAlexanderDualityH0Certificate (bicollarSliceMap Φ c)) :
    SphereSides (sliceImage Φ c) := by
  have hcont : Continuous (bicollarSliceMap Φ c) := by
    exact hΦ.contMDiff.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hcompact : IsCompact (Set.range (bicollarSliceMap Φ c)) :=
    isCompact_range hcont
  have hconnected : IsConnected (Set.range (bicollarSliceMap Φ c)) := by
    simpa only [_root_.Set.image_univ] using
      isConnected_sphereTwo.image (bicollarSliceMap Φ c)
        hcont.continuousOn
  rw [← range_bicollarSliceMap Φ c]
  exact topologicalSphereSidesOfAlexanderDualityData
    (bicollarSliceMap Φ c) hcompact hconnected
    (by
      rw [range_bicollarSliceMap Φ c]
      exact locallyTwoSided_sliceImage Φ hΦ c)
    hAD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSides_bicollarSlice_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSides_bicollarSlice_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSides_bicollarSlice_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSides_bicollarSlice_of_alexanderDuality

theorem sliceImage_equiv_comp
    {N M : Type*} {a : ℝ} (ψ : N ≃ M)
    (Φ : SphereTwo × AxialInterval a → N) (c : AxialInterval a) :
    sliceImage (ψ ∘ Φ) c = ψ '' sliceImage Φ c := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Φ p, ⟨p, hp, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.sliceImage_equiv_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.sliceImage_equiv_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.sliceImage_equiv_comp ``Submission.DifferentialGeometry.Topology.SphereSeparation.sliceImage_equiv_comp

noncomputable def topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (c : AxialInterval a)
    (hAD : HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) c)) :
    SphereSides (sliceImage Φ c) := by
  have hΦℝ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ (ψ ∘ Φ) :=
    hΦ.postcomp_diffeomorph ψ
  let dℝ : SphereSides (sliceImage (ψ ∘ Φ) c) :=
    topologicalSphereSides_bicollarSlice_of_alexanderDuality
      (ψ ∘ Φ) hΦℝ c hAD
  have himage :
      sliceImage (ψ ∘ Φ) c = ψ '' sliceImage Φ c :=
    sliceImage_equiv_comp ψ.toEquiv Φ c
  have hback : ψ.symm '' sliceImage (ψ ∘ Φ) c = sliceImage Φ c := by
    rw [himage, Set.image_image]
    simp only [ψ.symm_apply_apply, Set.image_id']
  rw [← hback]
  exact dℝ.imageDiffeomorph ψ.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality

noncomputable def bicollarSliceSidesOpenThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : ∀ c, HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) c))
    (c : AxialInterval a) :
    SphereSides (sliceImage Φ c) :=
  topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
    Φ hΦ ψ c (hAD c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollarSliceSidesOpenThreeSpace_of_alexanderDuality

theorem bicollar_sides_openThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [ChartedSpace EuclideanThree N]
    {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) (axialZero ha))) :
    let d :=
      topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
        Φ hΦ ψ (axialZero ha) hAD
    Xor
      (negativeHalfImage Φ ha ⊆ d.compactSide ∧
        positiveHalfImage Φ ha ⊆ d.endSide)
      (negativeHalfImage Φ ha ⊆ d.endSide ∧
        positiveHalfImage Φ ha ⊆ d.compactSide) := by
  let d :=
    topologicalSphereSidesOpenThreeSpace_bicollarSlice_of_alexanderDuality
      Φ hΦ ψ (axialZero ha) hAD
  change Xor
    (negativeHalfImage Φ ha ⊆ d.compactSide ∧
      positiveHalfImage Φ ha ⊆ d.endSide)
    (negativeHalfImage Φ ha ⊆ d.endSide ∧
      positiveHalfImage Φ ha ⊆ d.compactSide)
  change SphereSides (zeroSliceImage Φ ha) at d
  exact bicollar_halves_opposite ha Φ hΦ d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_sides_openThreeSpace_of_alexanderDuality

theorem bicollar_order_openThreeSpace_of_alexanderDuality
    {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace EuclideanThree N] {a : ℝ} (ha : 0 < a)
    (Φ : SphereTwo × AxialInterval a → N)
    (hΦ : Manifold.IsSmoothEmbedding
      ((𝓘(ℝ, EuclideanSpace ℝ (Fin 2))).prod 𝓘(ℝ))
      (𝓘(ℝ, EuclideanThree)) ∞ Φ)
    (ψ : Diffeomorph (𝓘(ℝ, EuclideanThree)) (𝓘(ℝ, EuclideanThree))
      N EuclideanThree ∞)
    (hAD : ∀ c, HasAlexanderDualityH0Certificate
      (bicollarSliceMap (ψ ∘ Φ) c))
    (o₀ : IsAxiallyOrientedAtZero ha Φ
      (bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD))
    {s t : AxialInterval a} (hst : s < t) :
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
  exact bicollar_order_of_atZero ha Φ hΦ
    (bicollarSliceSidesOpenThreeSpace_of_alexanderDuality Φ hΦ ψ hAD)
    o₀ hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_alexanderDuality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_alexanderDuality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_alexanderDuality ``Submission.DifferentialGeometry.Topology.SphereSeparation.bicollar_order_openThreeSpace_of_alexanderDuality

end DifferentialGeometry.Topology.SphereSeparation
