import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OpenExcision
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
import Mathlib.Topology.Sets.Compacts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.Set _root_.TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : Set X) (hK : IsClosed (f '' K)) :
    Function.Bijective (integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
        MapsTo f Kᶜ (f '' K)ᶜ)) := by
  let A : Set Y := (f '' K)ᶜ
  let B : Set Y := _root_.Set.range f
  let e : X ≃ₜ B := hf.isEmbedding.toHomeomorph
  let g : ContinuousMap X B := ⟨e, e.continuous⟩
  have hg : _root_.Set.MapsTo g Kᶜ (subspaceIntersection A B) := by
    intro x hx
    exact _root_.Set.image_compl_subset hf.injective ⟨x, hx, rfl⟩
  have hg' : _root_.Set.MapsTo e.symm (subspaceIntersection A B) Kᶜ := by
    intro y hy hx
    apply hy
    refine ⟨e.symm y, hx, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply y)
  have hgbij : Function.Bijective (integralRelativeHomologyMap n g hg) := by
    let E := integralRelativeHomologyHomeomorphIso n e Kᶜ (subspaceIntersection A B) hg hg'
    exact ⟨(ModuleCat.mono_iff_injective E.hom).mp inferInstance,
      (ModuleCat.epi_iff_surjective E.hom).mp inferInstance⟩
  have hcover : A ∪ B = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ f '' K
    · obtain ⟨x, hx, rfl⟩ := hy
      exact Or.inr ⟨x, rfl⟩
    · exact Or.inl hy
  have hibij : Function.Bijective (integralRelativeHomologyMap n (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B)) := by
    let E := integralRelativeOpenExcisionIso n A B hK.isOpen_compl hf.isOpen_range hcover
    exact ⟨(ModuleCat.mono_iff_injective E.hom).mp inferInstance,
      (ModuleCat.epi_iff_surjective E.hom).mp inferInstance⟩
  have heq := integralRelativeHomologyMap_comp n g (singularSubspaceInclusion B)
    hg (subspaceIntersection_mapsTo A B)
  change integralRelativeHomologyMap n f _ = _ at heq
  rw [heq]
  exact hibij.comp hgbij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image

theorem integralRelativeHomologyMap_bijective_of_isOpenEmbedding [T2Space Y]
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : _root_.TopologicalSpace.Compacts X) :
    Function.Bijective (integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
        MapsTo f (K : Set X)ᶜ (f '' (K : Set X))ᶜ)) :=
  integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image n f hf
    (K : Set X) (K.isCompact.image f.continuous).isClosed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_bijective_of_isOpenEmbedding

end DifferentialGeometry.Topology

end
