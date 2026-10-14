import Submission.DifferentialGeometry.Topology.Homology.RelativeOpenEmbedding

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.Set _root_.TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private theorem relativeHomologyMap_compact_map_comp
    (n : ℕ) (f : ContinuousMap Y Z) (g : ContinuousMap Z X)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (K : _root_.TopologicalSpace.Compacts Y) (c : integralRelativeHomology n (K : Set Y)ᶜ)
    (cX : ∀ L : _root_.TopologicalSpace.Compacts X, integralRelativeHomology n (L : Set X)ᶜ)
    (hc : integralRelativeHomologyMap n (g.comp f)
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset (hg.comp hf))) c =
        cX (K.map (g.comp f) (g.comp f).continuous)) :
    integralRelativeHomologyMap n g
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hg))
        (integralRelativeHomologyMap n f
          (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf)) c) =
      cX ((K.map f f.continuous).map g g.continuous) := by
  let L := K.map f f.continuous
  let M := L.map g g.continuous
  let hF : _root_.Set.MapsTo f (K : Set Y)ᶜ (L : Set Z)ᶜ :=
    mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf)
  let hG : _root_.Set.MapsTo g (L : Set Z)ᶜ (M : Set X)ᶜ :=
    mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hg)
  have heq := Compacts.map_comp g f g.continuous f.continuous K
  have aux (N : _root_.TopologicalSpace.Compacts X) (hN : K.map (g.comp f) (g.comp f).continuous = N)
      (hmap : _root_.Set.MapsTo (g.comp f) (K : Set Y)ᶜ (N : Set X)ᶜ) :
      integralRelativeHomologyMap n (g.comp f) hmap c = cX N := by
    subst N
    exact hc
  have h := aux M heq (hG.comp hF)
  rw [integralRelativeHomologyMap_comp, LinearMap.comp_apply] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.relativeHomologyMap_compact_map_comp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.relativeHomologyMap_compact_map_comp target :: scope.openDecls } }

theorem integralRelativeHomology_family_map_of_comp [T2Space X]
    (n : ℕ) (f : ContinuousMap Y Z) (g : ContinuousMap Z X)
    (hf : Function.Injective f) (hg : _root_.Topology.IsOpenEmbedding g)
    (cY : ∀ K : _root_.TopologicalSpace.Compacts Y, integralRelativeHomology n (K : Set Y)ᶜ)
    (cZ : ∀ L : _root_.TopologicalSpace.Compacts Z, integralRelativeHomology n (L : Set Z)ᶜ)
    (cX : ∀ M : _root_.TopologicalSpace.Compacts X, integralRelativeHomology n (M : Set X)ᶜ)
    (hY : ∀ K : _root_.TopologicalSpace.Compacts Y,
      integralRelativeHomologyMap n (g.comp f)
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset (hg.injective.comp hf))) (cY K) =
          cX (K.map (g.comp f) (g.comp f).continuous))
    (hZ : ∀ L : _root_.TopologicalSpace.Compacts Z,
      integralRelativeHomologyMap n g
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hg.injective)) (cZ L) =
          cX (L.map g g.continuous)) :
    ∀ K : _root_.TopologicalSpace.Compacts Y,
      integralRelativeHomologyMap n f
        (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf)) (cY K) =
          cZ (K.map f f.continuous) := by
  intro K
  apply (integralRelativeHomologyMap_bijective_of_isOpenEmbedding n g hg
    (K.map f f.continuous)).injective
  exact (relativeHomologyMap_compact_map_comp n f g hf hg.injective K (cY K) cX (hY K)).trans
    (hZ (K.map f f.continuous)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomology_family_map_of_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomology_family_map_of_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomology_family_map_of_comp ``Submission.DifferentialGeometry.Topology.integralRelativeHomology_family_map_of_comp

end DifferentialGeometry.Topology

end
