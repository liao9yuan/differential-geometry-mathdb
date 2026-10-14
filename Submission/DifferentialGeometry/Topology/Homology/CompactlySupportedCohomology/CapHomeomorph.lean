import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CompactlySupportedCohomology.CapNaturality
import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.Homeomorph
import Submission.DifferentialGeometry.Topology.Homology.CompactHomologyOpenEmbedding
import Submission.DifferentialGeometry.Topology.Homology.CompactHomologyLocalGenerators

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace

universe u

namespace DifferentialGeometry.Topology

theorem integralCompactlySupportedCohomology_cap_bijective_of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (k m : ℕ) (e : X ≃ₜ Y)
    (cY : ∀ K : _root_.TopologicalSpace.Compacts Y, integralRelativeHomology (k + m) (K : Set Y)ᶜ)
    (hY : ∀ (K L : _root_.TopologicalSpace.Compacts Y) (h : K ≤ L),
      integralRelativeHomologyMap (k + m) (ContinuousMap.id Y)
        (show _root_.Set.MapsTo (ContinuousMap.id Y) (L : Set Y)ᶜ (K : Set Y)ᶜ from
          compl_subset_compl.mpr h) (cY L) = cY K)
    (hpoints : ∀ p : Y, Function.Bijective (fun z : ℤ => z • cY {p}))
    (hXcap : ∀ (cX : ∀ K : _root_.TopologicalSpace.Compacts X,
        integralRelativeHomology (k + m) (K : Set X)ᶜ),
      (∀ (K L : _root_.TopologicalSpace.Compacts X) (h : K ≤ L),
        integralRelativeHomologyMap (k + m) (ContinuousMap.id X)
          (show _root_.Set.MapsTo (ContinuousMap.id X) (L : Set X)ᶜ (K : Set X)ᶜ from
            compl_subset_compl.mpr h) (cX L) = cX K) →
      (∀ p : X, Function.Bijective (fun z : ℤ => z • cX {p})) →
      ∀ (DX : integralCompactlySupportedCohomology k X →ₗ[ℤ]
        integralSingularHomology m X),
      (∀ (K : _root_.TopologicalSpace.Compacts X) (α : integralRelativeCohomology k (K : Set X)ᶜ),
        DX (integralRelativeToCompactlySupportedCohomology k K α) =
          integralRelativeCohomologyCapToAbsolute (K : Set X)ᶜ k m α (cX K)) →
      Function.Bijective DX)
    (DY : integralCompactlySupportedCohomology k Y →ₗ[ℤ]
      integralSingularHomology m Y)
    (hDY : ∀ (L : _root_.TopologicalSpace.Compacts Y) (β : integralRelativeCohomology k (L : Set Y)ᶜ),
      DY (integralRelativeToCompactlySupportedCohomology k L β) =
        integralRelativeCohomologyCapToAbsolute (L : Set Y)ᶜ k m β (cY L)) :
    Function.Bijective DY := by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  obtain ⟨cX, ⟨hX, htransport⟩, _⟩ :=
    exists_unique_compact_homology_family_of_isOpenEmbedding (k + m) f
      e.isOpenEmbedding cY hY
  have hpointsX : ∀ p : X, Function.Bijective (fun z : ℤ => z • cX {p}) := by
    intro p
    exact (compact_homology_family_local_generator_iff_of_isOpenEmbedding
      (k + m) f e.isOpenEmbedding p cX cY (htransport {p})).mpr (hpoints (f p))
  obtain ⟨DX, DY', hDX, hDY', hnat⟩ :=
    exists_integralCompactlySupportedCohomology_cap_natural
      k m f e.isOpenEmbedding cX cY hX hY htransport
  have hDXbij : Function.Bijective DX := hXcap cX hX hpointsX DX hDX
  have hhom : Function.Bijective (integralSingularHomologyMap m f) := by
    exact ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) m).obj
      integralSingularCoefficients).mapIso
        (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e)).toLinearEquiv).bijective
  have hDY'bij : Function.Bijective DY' := by
    apply (Function.Bijective.of_comp_iff DY'
      (integralCompactlySupportedCohomologyPushforward_homeomorph_bijective k e)).mp
    have hbij := hhom.comp hDXbij
    change Function.Bijective ((integralSingularHomologyMap m f).comp DX) at hbij
    rw [hnat] at hbij
    exact hbij
  have hEq : DY = DY' := integralCompactlySupportedCohomology_hom_ext k
    (fun K α => (hDY K α).trans (hDY' K α).symm)
  rw [hEq]
  exact hDY'bij

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_homeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_homeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_homeomorph ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_cap_bijective_of_homeomorph

end DifferentialGeometry.Topology

end
