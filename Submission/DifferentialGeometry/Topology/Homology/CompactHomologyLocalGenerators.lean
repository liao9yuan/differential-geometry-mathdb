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

theorem integralRelativeHomology_generator_bijective_iff_of_isOpenEmbedding
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (n : ℕ) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (p : X)
    (a : integralRelativeHomology n ({p}ᶜ : Set X))
    (b : integralRelativeHomology n ({f p}ᶜ : Set Y))
    (hab : integralRelativeHomologyMap n f
      (show _root_.Set.MapsTo f ({p}ᶜ : Set X) ({f p}ᶜ : Set Y) from
        fun _ hx h => hx (hf.injective h)) a = b) :
    Function.Bijective (fun z : ℤ => z • a) ↔ Function.Bijective (fun z : ℤ => z • b) := by
  have hmap := integralRelativeHomologyMap_bijective_of_isOpenEmbedding_of_isClosed_image
    n f hf {p} (by rw [Set.image_singleton]; exact isClosed_singleton)
  have hmap' (B : Set Y) (hB : B = f '' ({p} : Set X))
      (hAB : _root_.Set.MapsTo f ({p}ᶜ : Set X) Bᶜ) :
      Function.Bijective (integralRelativeHomologyMap n f hAB) := by
    subst B
    exact hmap
  have hlocal := hmap' {f p} Set.image_singleton.symm
    (fun _ hx h => hx (hf.injective h))
  have hcomp : integralRelativeHomologyMap n f
      (show _root_.Set.MapsTo f ({p}ᶜ : Set X) ({f p}ᶜ : Set Y) from
        fun _ hx h => hx (hf.injective h)) ∘
      (fun z : ℤ => z • a) = fun z : ℤ => z • b := by
    funext z
    rw [Function.comp_apply, map_zsmul, hab]
  rw [← hcomp]
  exact (hlocal.of_comp_iff' (fun z : ℤ => z • a)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomology_generator_bijective_iff_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomology_generator_bijective_iff_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomology_generator_bijective_iff_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.integralRelativeHomology_generator_bijective_iff_of_isOpenEmbedding


theorem compact_homology_family_local_generator_iff_of_isOpenEmbedding
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space Y]
    (n : ℕ) (f : C(X, Y)) (hf : _root_.Topology.IsOpenEmbedding f) (p : X)
    (cX : ∀ K : _root_.TopologicalSpace.Compacts X, integralRelativeHomology n (K : Set X)ᶜ)
    (cY : ∀ L : _root_.TopologicalSpace.Compacts Y, integralRelativeHomology n (L : Set Y)ᶜ)
    (htransport : integralRelativeHomologyMap n f
      (mapsTo_iff_image_subset.mpr (_root_.Set.image_compl_subset hf.injective)) (cX {p}) =
        cY (({p} : _root_.TopologicalSpace.Compacts X).map f f.continuous)) :
    Function.Bijective (fun z : ℤ => z • cX {p}) ↔
      Function.Bijective (fun z : ℤ => z • cY {f p}) := by
  have hpoint : integralRelativeHomologyMap n f
      (show _root_.Set.MapsTo f ({p}ᶜ : Set X) ({f p}ᶜ : Set Y) from
        fun _ hx h => hx (hf.injective h)) (cX {p}) = cY {f p} := by
    have h (K : _root_.TopologicalSpace.Compacts Y) (hK : K = ({p} : _root_.TopologicalSpace.Compacts X).map f f.continuous)
        (hAB : _root_.Set.MapsTo f ({p}ᶜ : Set X) (K : Set Y)ᶜ) :
        integralRelativeHomologyMap n f hAB (cX {p}) = cY K := by
      subst K
      exact htransport
    exact h {f p} (Compacts.map_singleton f.continuous p).symm _
  exact integralRelativeHomology_generator_bijective_iff_of_isOpenEmbedding
    n f hf p (cX {p}) (cY {f p}) hpoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compact_homology_family_local_generator_iff_of_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compact_homology_family_local_generator_iff_of_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compact_homology_family_local_generator_iff_of_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.compact_homology_family_local_generator_iff_of_isOpenEmbedding

end DifferentialGeometry.Topology

end
