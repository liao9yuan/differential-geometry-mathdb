import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.Defs
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainExcision

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
private theorem compact_support_excision_mapsTo (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) (K : _root_.TopologicalSpace.Compacts X) :
    MapsTo f (K : Set X)ᶜ (K.map f f.continuous : Set Y)ᶜ :=
  mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_support_excision_mapsTo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_support_excision_mapsTo target :: scope.openDecls } }

private def compactSupportExcision (n : ℕ) (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) (K : _root_.TopologicalSpace.Compacts X) :
    integralRelativeCohomology n (K.map f f.continuous : Set Y)ᶜ ≃ₗ[ℤ]
      integralRelativeCohomology n (K : Set X)ᶜ :=
  LinearEquiv.ofBijective (integralRelativeCohomologyMap n f
    (compact_support_excision_mapsTo f hf K))
    (integralRelativeCohomologyMap_bijective_of_isOpenEmbedding n f hf K)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compactSupportExcision
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compactSupportExcision target :: scope.openDecls } }

private theorem compact_support_excision_natural (n : ℕ) (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L)
    (β : integralRelativeCohomology n (K.map f f.continuous : Set Y)ᶜ) :
    compactSupportExcision n f hf L
        (integralRelativeCohomologyMap n (ContinuousMap.id Y)
          (show _root_.Set.MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
            (K.map f f.continuous : Set Y)ᶜ from
              compl_subset_compl.mpr (_root_.Set.image_mono h)) β) =
      integralRelativeCohomologyMap n (ContinuousMap.id X)
        (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
          compl_subset_compl.mpr h) (compactSupportExcision n f hf K β) := by
  have h₁ := integralRelativeCohomologyMap_comp n f (ContinuousMap.id Y)
    (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
      _root_.Set.MapsTo f (L : Set X)ᶜ (L.map f f.continuous : Set Y)ᶜ)
    (show _root_.Set.MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
      (K.map f f.continuous : Set Y)ᶜ from
        compl_subset_compl.mpr (_root_.Set.image_mono h))
  have h₂ := integralRelativeCohomologyMap_comp n (ContinuousMap.id X) f
    (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr h)
    (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective) :
      _root_.Set.MapsTo f (K : Set X)ᶜ (K.map f f.continuous : Set Y)ᶜ)
  exact LinearMap.congr_fun (h₁.symm.trans h₂) β

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_support_excision_natural
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_support_excision_natural target :: scope.openDecls } }

def integralCompactlySupportedCohomologyPushforward (n : ℕ) (f : ContinuousMap X Y)
    (hf : _root_.Topology.IsOpenEmbedding f) :
    integralCompactlySupportedCohomology n X →ₗ[ℤ]
      integralCompactlySupportedCohomology n Y :=
  integralCompactlySupportedCohomologyDesc n
    (fun K => (integralRelativeToCompactlySupportedCohomology n
      (K.map f f.continuous)).comp (compactSupportExcision n f hf K).symm.toLinearMap)
    (by
      intro K L h α
      have heq : (compactSupportExcision n f hf L).symm
          (integralRelativeCohomologyMap n (ContinuousMap.id X)
            (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
              compl_subset_compl.mpr h) α) =
          integralRelativeCohomologyMap n (ContinuousMap.id Y)
            (show _root_.Set.MapsTo (ContinuousMap.id Y) (L.map f f.continuous : Set Y)ᶜ
              (K.map f f.continuous : Set Y)ᶜ from
                compl_subset_compl.mpr (_root_.Set.image_mono h))
            ((compactSupportExcision n f hf K).symm α) := by
        apply (compactSupportExcision n f hf L).injective
        rw [LinearEquiv.apply_symm_apply,
          compact_support_excision_natural n f hf K L h,
          LinearEquiv.apply_symm_apply]
      change integralRelativeToCompactlySupportedCohomology n (L.map f f.continuous)
        ((compactSupportExcision n f hf L).symm _) = _
      rw [heq]
      exact integralRelativeToCompactlySupportedCohomology_map n
        (K.map f f.continuous) (L.map f f.continuous) (_root_.Set.image_mono h) _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward

private theorem compact_support_pushforward_representative
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f) (K : _root_.TopologicalSpace.Compacts X)
    (α : integralRelativeCohomology n (K : Set X)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n f hf
        (integralRelativeToCompactlySupportedCohomology n K α) =
      integralRelativeToCompactlySupportedCohomology n (K.map f f.continuous)
        ((compactSupportExcision n f hf K).symm α) :=
  integralCompactlySupportedCohomologyDesc_representative n _ _ K α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_support_pushforward_representative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_support_pushforward_representative target :: scope.openDecls } }

theorem integralCompactlySupportedCohomologyPushforward_relative
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f) (K : _root_.TopologicalSpace.Compacts X)
    (β : integralRelativeCohomology n (K.map f f.continuous : Set Y)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n f hf
        (integralRelativeToCompactlySupportedCohomology n K
          (integralRelativeCohomologyMap n f
            (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)) β)) =
      integralRelativeToCompactlySupportedCohomology n (K.map f f.continuous) β := by
  rw [compact_support_pushforward_representative]
  exact congrArg (integralRelativeToCompactlySupportedCohomology n (K.map f f.continuous))
    ((compactSupportExcision n f hf K).symm_apply_apply β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_relative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_relative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_relative ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_relative

private theorem compact_support_pushforward_relative_of_eq
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (K : _root_.TopologicalSpace.Compacts X) (L : _root_.TopologicalSpace.Compacts Y) (h : K.map f f.continuous = L)
    (hρ : _root_.Set.MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ)
    (β : integralRelativeCohomology n (L : Set Y)ᶜ) :
    integralCompactlySupportedCohomologyPushforward n f hf
        (integralRelativeToCompactlySupportedCohomology n K
          (integralRelativeCohomologyMap n f hρ β)) =
      integralRelativeToCompactlySupportedCohomology n L β := by
  subst L
  exact integralCompactlySupportedCohomologyPushforward_relative n f hf K β

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.compact_support_pushforward_relative_of_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.compact_support_pushforward_relative_of_eq target :: scope.openDecls } }

theorem integralCompactlySupportedCohomologyPushforward_forget
    (n : ℕ) (f : ContinuousMap X Y) (hf : _root_.Topology.IsOpenEmbedding f) :
    (integralSingularCohomologyMap n f).comp
        ((integralCompactlySupportedToSingularCohomology n Y).comp
          (integralCompactlySupportedCohomologyPushforward n f hf)) =
      integralCompactlySupportedToSingularCohomology n X := by
  apply integralCompactlySupportedCohomology_hom_ext n
  intro K α
  let hρ := compact_support_excision_mapsTo f hf K
  obtain ⟨β, hβ⟩ := (compactSupportExcision n f hf K).surjective α
  change integralRelativeCohomologyMap n f hρ β = α at hβ
  simp only [LinearMap.comp_apply]
  rw [← hβ, compact_support_pushforward_relative_of_eq n f hf K
    (K.map f f.continuous) rfl hρ β,
    integralCompactlySupportedToSingularCohomology_representative,
    integralCompactlySupportedToSingularCohomology_representative]
  exact (LinearMap.congr_fun (integralRelativeToAbsoluteCohomology_natural n f hρ) β).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_forget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_forget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_forget ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_forget

theorem integralCompactlySupportedCohomologyPushforward_id
    {X : Type u} [TopologicalSpace X] [T2Space X] (n : ℕ) :
    integralCompactlySupportedCohomologyPushforward n (ContinuousMap.id X)
      _root_.Topology.IsOpenEmbedding.id = LinearMap.id := by
  apply integralCompactlySupportedCohomology_hom_ext n
  intro K α
  have hmap : K.map (ContinuousMap.id X) (ContinuousMap.id X).continuous = K :=
    Compacts.map_id K
  have h := compact_support_pushforward_relative_of_eq n (ContinuousMap.id X)
    _root_.Topology.IsOpenEmbedding.id K K hmap (show _root_.Set.MapsTo (ContinuousMap.id X)
      (K : Set X)ᶜ (K : Set X)ᶜ from fun _ hx => hx) α
  rw [integralRelativeCohomologyMap_id, LinearMap.id_apply] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_id ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_id

theorem integralCompactlySupportedCohomologyPushforward_comp
    {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    (n : ℕ) (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    (hf : _root_.Topology.IsOpenEmbedding f) (hg : _root_.Topology.IsOpenEmbedding g) :
    integralCompactlySupportedCohomologyPushforward n (g.comp f) (hg.comp hf) =
      (integralCompactlySupportedCohomologyPushforward n g hg).comp
        (integralCompactlySupportedCohomologyPushforward n f hf) := by
  apply integralCompactlySupportedCohomology_hom_ext n
  intro K α
  let L := K.map f f.continuous
  let N := L.map g g.continuous
  let hρf : _root_.Set.MapsTo f (K : Set X)ᶜ (L : Set Y)ᶜ :=
    compact_support_excision_mapsTo f hf K
  let hρg : _root_.Set.MapsTo g (L : Set Y)ᶜ (N : Set Z)ᶜ :=
    compact_support_excision_mapsTo g hg L
  obtain ⟨δ, hδ⟩ := (compactSupportExcision n f hf K).surjective α
  change integralRelativeCohomologyMap n f hρf δ = α at hδ
  obtain ⟨β, hβ⟩ := (compactSupportExcision n g hg L).surjective δ
  change integralRelativeCohomologyMap n g hρg β = δ at hβ
  simp only [LinearMap.comp_apply]
  rw [← hδ, ← hβ,
    compact_support_pushforward_relative_of_eq n f hf K L rfl hρf,
    compact_support_pushforward_relative_of_eq n g hg L N rfl hρg]
  have hmap : K.map (g.comp f) (g.comp f).continuous = N :=
    Compacts.map_comp g f g.continuous f.continuous K
  have hcomp := LinearMap.congr_fun (integralRelativeCohomologyMap_comp n f g hρf hρg) β
  have heq := congrArg (fun γ : integralRelativeCohomology n (K : Set X)ᶜ =>
    integralCompactlySupportedCohomologyPushforward n (g.comp f) (hg.comp hf)
      (integralRelativeToCompactlySupportedCohomology n K γ)) hcomp
  exact heq.symm.trans (compact_support_pushforward_relative_of_eq n (g.comp f)
    (hg.comp hf) K N hmap (hρg.comp hρf) β)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_comp ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_comp

end DifferentialGeometry.Topology

end
