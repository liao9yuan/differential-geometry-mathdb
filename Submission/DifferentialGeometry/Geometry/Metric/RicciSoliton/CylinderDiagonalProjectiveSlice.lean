import Submission.DifferentialGeometry.Topology.ProjectiveSpace.SmoothNonembedding
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph
import Submission.DifferentialGeometry.Topology.ProjectiveSpace.CylinderProjectiveSlice
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import Submission.DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
open private exists_diffeomorph_orbitQuotient from Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "ThreeSpace" => EuclideanSpace ℝ (Fin 3)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold (𝓡 3) ∞ M] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold (𝓡 3) ∞ N]

theorem exists_projective_slice_diagonal_image
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ⊆
      Phi.source) :
    ∃ e : SphereAntipodalQuotient → N,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e ∧
      (∀ z : SphereTwo, e (SphereAntipodalQuotient.proj z) =
        Phi (d (Geometry.cylinderDiagonalQuotientMap (z, 0)))) ∧
      _root_.Set.range e = Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
        (_root_.Set.univ ×ˢ ({0} : Set ℝ)))) ∧
      _root_.Set.range e ⊆ Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
        (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L))) := by
  obtain ⟨D, hD⟩ := exists_diffeomorph_orbitQuotient
  let f : SphereAntipodalQuotient → M :=
    (D.trans d) ∘ CylinderDiagonalQuotient.projectiveSlice
  have hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    (diffeomorph_isSmoothEmbedding (D.trans d)).comp
      CylinderDiagonalQuotient.isSmoothEmbedding_projectiveSlice (by simp)
  have hfproj (z : SphereTwo) : f (SphereAntipodalQuotient.proj z) =
      d (Geometry.cylinderDiagonalQuotientMap (z, 0)) := by
    change d (D (CylinderDiagonalQuotient.projectiveSlice
      (SphereAntipodalQuotient.proj z))) = _
    rw [CylinderDiagonalQuotient.projectiveSlice_proj, hD]
  have hfrange : _root_.Set.range f = d '' (Geometry.cylinderDiagonalQuotientMap ''
      (_root_.Set.univ ×ˢ ({0} : Set ℝ))) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := SphereAntipodalQuotient.surjective_proj z
      exact ⟨Geometry.cylinderDiagonalQuotientMap (w, 0),
        ⟨(w, 0), ⟨mem_univ _, rfl⟩, rfl⟩, (hfproj w).symm⟩
    · rintro ⟨z, ⟨⟨w, s⟩, ⟨_, hs⟩, rfl⟩, rfl⟩
      have hs0 : s = 0 := hs
      subst s
      exact ⟨SphereAntipodalQuotient.proj w, hfproj w⟩
  have hslab : d '' (Geometry.cylinderDiagonalQuotientMap ''
      (_root_.Set.univ ×ˢ ({0} : Set ℝ))) ⊆
      d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) := by
    apply _root_.Set.image_mono
    apply _root_.Set.image_mono
    intro z hz
    have hz0 : z.2 = 0 := hz.2
    exact ⟨mem_univ _, hz0.symm ▸ ⟨neg_nonpos.mpr hL, hL⟩⟩
  have hfsrc : _root_.Set.range f ⊆ Phi.source := by
    rw [hfrange]
    exact hslab.trans hsource
  refine ⟨Phi ∘ f,
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph Phi hf hfsrc,
    ?_, ?_, ?_⟩
  · intro z
    exact congrArg Phi (hfproj z)
  · rw [_root_.Set.range_comp, hfrange]
  · rw [_root_.Set.range_comp, hfrange]
    exact _root_.Set.image_mono hslab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_projective_slice_diagonal_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_projective_slice_diagonal_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_projective_slice_diagonal_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_projective_slice_diagonal_image

theorem not_diagonal_slab_image_subset_partialDiffeomorph_target
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ⊆
      Phi.source)
    (chart : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace N ∞) :
    ¬ Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
      (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L))) ⊆ chart.target := by
  obtain ⟨e, he, _, _, hsub⟩ := exists_projective_slice_diagonal_image d Phi hL hsource
  intro hchart
  exact SphereAntipodalQuotient.not_range_subset_partialDiffeomorph_target e he chart
    (hsub.trans hchart)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_target ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_target

theorem not_diagonal_slab_image_subset_partialDiffeomorph_image
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L)) ⊆
      Phi.source)
    (chart : PartialDiffeomorph (𝓡 3) (𝓡 3) ThreeSpace N ∞)
    {A : Set ThreeSpace} (hA : A ⊆ chart.source) :
    ¬ Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap ''
      (_root_.Set.univ ×ˢ _root_.Set.Icc (-L) L))) ⊆ chart '' A := by
  intro hsub
  apply not_diagonal_slab_image_subset_partialDiffeomorph_target d Phi hL hsource chart
  apply hsub.trans
  rintro y ⟨z, hz, rfl⟩
  exact chart.map_source (hA hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.not_diagonal_slab_image_subset_partialDiffeomorph_image

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
