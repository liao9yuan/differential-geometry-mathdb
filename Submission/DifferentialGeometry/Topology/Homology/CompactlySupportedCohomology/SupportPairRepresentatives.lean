import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.RelativeSupport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem integralCompactlySupportedCohomologyOn_union_exists_representative
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (α : integralCompactlySupportedCohomology n ↥(U ∪ V)) :
    ∃ (A B : _root_.TopologicalSpace.Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
      (β : integralRelativeCohomology n ((A ⊔ B : _root_.TopologicalSpace.Compacts X) : Set X)ᶜ),
      integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (_root_.Set.union_subset_union hA hB) β = α := by
  obtain ⟨K, hK, γ, hγ⟩ := integralCompactlySupportedCohomologyOn_exists_representative
    n (U ∪ V) (hU.union hV) α
  obtain ⟨A, B, hAc, hBc, hAU, hBV, hAB⟩ := K.isCompact.binary_compact_cover hU hV hK
  let KA : _root_.TopologicalSpace.Compacts X := ⟨A, hAc⟩
  let KB : _root_.TopologicalSpace.Compacts X := ⟨B, hBc⟩
  have hKAB : K ≤ KA ⊔ KB := by
    change (K : Set X) ⊆ A ∪ B
    rw [hAB]
  let β := integralRelativeCohomologyMap n (ContinuousMap.id X)
    (show _root_.Set.MapsTo (ContinuousMap.id X) ((KA ⊔ KB : _root_.TopologicalSpace.Compacts X) : Set X)ᶜ (K : Set X)ᶜ from
      compl_subset_compl.mpr hKAB) γ
  refine ⟨KA, KB, hAU, hBV, β, ?_⟩
  exact (integralRelativeToCompactlySupportedCohomologyOn_mono n (U ∪ V) K (KA ⊔ KB)
    hKAB hK (_root_.Set.union_subset_union hAU hBV) γ).trans hγ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_exists_representative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_exists_representative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_exists_representative ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_exists_representative

theorem integralCompactlySupportedCohomologyOn_union_hom_ext
    (n : ℕ) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    {P : Type*} [AddCommMonoid P] [Module ℤ P]
    {f g : integralCompactlySupportedCohomology n ↥(U ∪ V) →ₗ[ℤ] P}
    (h : ∀ (A B : _root_.TopologicalSpace.Compacts X) (hA : (A : Set X) ⊆ U) (hB : (B : Set X) ⊆ V)
      (β : integralRelativeCohomology n ((A ⊔ B : _root_.TopologicalSpace.Compacts X) : Set X)ᶜ),
      f (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (_root_.Set.union_subset_union hA hB) β) =
      g (integralRelativeToCompactlySupportedCohomologyOn n (U ∪ V) (A ⊔ B)
        (_root_.Set.union_subset_union hA hB) β)) : f = g := by
  ext α
  obtain ⟨A, B, hA, hB, β, rfl⟩ :=
    integralCompactlySupportedCohomologyOn_union_exists_representative n U V hU hV α
  exact h A B hA hB β

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_hom_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_hom_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_hom_ext ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyOn_union_hom_ext

end DifferentialGeometry.Topology
