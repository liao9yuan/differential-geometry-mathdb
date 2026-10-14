import Submission.DifferentialGeometry.Topology.Homology.RelativeOpenEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]

omit [T2Space Y] in
private theorem compact_homology_open_embedding_restriction
    (n : ℕ) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L)
    (a : integralRelativeHomology n (L : Set X)ᶜ) :
    integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective))
      (integralRelativeHomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) a) =
    integralRelativeHomologyMap n (ContinuousMap.id Y)
      (show _root_.Set.MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
        (K.map f f.continuous : Set Y)ᶜ from compl_subset_compl.mpr (_root_.Set.image_mono h))
      (integralRelativeHomologyMap n f
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)) a) := by
  have h₁ := integralRelativeHomologyMap_comp n (ContinuousMap.id X) f
    (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr h)
    (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
      _root_.Set.MapsTo f (K : Set X)ᶜ (K.map f f.continuous : Set Y)ᶜ)
  have h₂ := integralRelativeHomologyMap_comp n f (ContinuousMap.id Y)
    (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
      _root_.Set.MapsTo f (L : Set X)ᶜ (L.map f f.continuous : Set Y)ᶜ)
    (show _root_.Set.MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
      (K.map f f.continuous : Set Y)ᶜ from compl_subset_compl.mpr (_root_.Set.image_mono h))
  exact LinearMap.congr_fun (h₁.symm.trans h₂) a

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_homology_open_embedding_restriction
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_homology_open_embedding_restriction target :: scope.openDecls } }

theorem exists_unique_compact_homology_family_of_isOpenEmbedding
    (n : ℕ) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (cY : ∀ L : _root_.TopologicalSpace.Compacts Y, integralRelativeHomology n (L : Set Y)ᶜ)
    (hY : ∀ (K L : _root_.TopologicalSpace.Compacts Y) (h : K ≤ L),
      integralRelativeHomologyMap n (ContinuousMap.id Y)
        (show _root_.Set.MapsTo (ContinuousMap.id Y) (L : Set Y)ᶜ (K : Set Y)ᶜ from
          compl_subset_compl.mpr h) (cY L) = cY K) :
    ∃! cX : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology n (K : Set X)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr h) (cX L) = cX K) ∧
      ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomologyMap n f
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)) (cX K) =
          cY (K.map f f.continuous) := by
  let e (K : _root_.TopologicalSpace.Compacts X) : integralRelativeHomology n (K : Set X)ᶜ ≃ₗ[ℤ]
      integralRelativeHomology n (K.map f f.continuous : Set Y)ᶜ :=
    LinearEquiv.ofBijective (integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)))
      (integralRelativeHomologyMap_bijective_of_isOpenEmbedding n f hf K)
  let cX (K : _root_.TopologicalSpace.Compacts X) := (e K).symm (cY (K.map f f.continuous))
  have he (K : _root_.TopologicalSpace.Compacts X) : integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)) (cX K) =
      cY (K.map f f.continuous) := (e K).apply_symm_apply _
  refine ⟨cX, ⟨?_, he⟩, ?_⟩
  · intro K L h
    apply (e K).injective
    change integralRelativeHomologyMap n f _ _ = integralRelativeHomologyMap n f _ (cX K)
    rw [compact_homology_open_embedding_restriction n f hf K L h, he L, he K]
    exact hY (K.map f f.continuous) (L.map f f.continuous) (_root_.Set.image_mono h)
  · intro d hd
    funext K
    exact (e K).injective ((hd.2 K).trans (he K).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_isOpenEmbedding

theorem exists_unique_compact_homology_family_of_absolute_of_isOpenEmbedding
    (n : ℕ) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f)
    (a : integralSingularHomology n Y) :
    ∃! cX : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology n (K : Set X)ᶜ,
      (∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr h) (cX L) = cX K) ∧
      ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomologyMap n f
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)) (cX K) =
          integralAbsoluteToRelative n (K.map f f.continuous : Set Y)ᶜ a := by
  apply exists_unique_compact_homology_family_of_isOpenEmbedding n f hf
    (fun K => integralAbsoluteToRelative n (K : Set Y)ᶜ a)
  intro K L h
  have hn := LinearMap.congr_fun (integralAbsoluteToRelative_natural n (ContinuousMap.id Y)
    (show _root_.Set.MapsTo (ContinuousMap.id Y) (L : Set Y)ᶜ (K : Set Y)ᶜ from
      compl_subset_compl.mpr h)) a
  simpa only [LinearMap.comp_apply, integralSingularHomologyMap_id, LinearMap.id_apply] using hn.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_absolute_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_absolute_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_absolute_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.exists_unique_compact_homology_family_of_absolute_of_isOpenEmbedding

end DifferentialGeometry.Topology

end
