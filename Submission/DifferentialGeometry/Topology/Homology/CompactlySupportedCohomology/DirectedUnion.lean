import Submission.DifferentialGeometry.Topology.Homology.CompactlySupportedCohomology.RelativeSupport
import Mathlib.Topology.Compactness.Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.TopologicalSpace

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {ι : Type v} [Nonempty ι]

theorem integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover
    (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = _root_.Set.univ)
    (α : integralCompactlySupportedCohomology n X) :
    ∃ (i : ι) (β : integralCompactlySupportedCohomology n (U i)),
      integralCompactlySupportedCohomologyPushforward n (singularSubspaceInclusion (U i))
        (hU i).isOpenEmbedding_subtypeVal β = α := by
  obtain ⟨K, γ, rfl⟩ := integralCompactlySupportedCohomology_exists_representative n α
  obtain ⟨i, hKi⟩ := K.isCompact.elim_directed_cover U hU
    (by rw [hcover]; exact _root_.Set.subset_univ _) hdir
  exact ⟨i, integralRelativeToCompactlySupportedCohomologyOn n (U i) K hKi γ,
    integralRelativeToCompactlySupportedCohomologyOn_pushforward n (U i) (hU i) K hKi γ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomology_exists_representative_of_directed_open_cover

omit [Nonempty ι] in
theorem integralCompactlySupportedCohomologyPushforward_eq_zero_of_directed_open_cover
    (n : ℕ) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = _root_.Set.univ)
    (i : ι) (β : integralCompactlySupportedCohomology n (U i))
    (hβ : integralCompactlySupportedCohomologyPushforward n (singularSubspaceInclusion (U i))
      (hU i).isOpenEmbedding_subtypeVal β = 0) :
    ∃ (j : ι) (hij : U i ⊆ U j),
      integralCompactlySupportedCohomologyPushforward n (ContinuousMap.inclusion hij)
        (_root_.Topology.IsOpenEmbedding.inclusion hij
          ((hU i).preimage
            (continuous_subtype_val : Continuous ((Subtype.val : U j → X))))) β = 0 := by
  let : Nonempty ι := ⟨i⟩
  obtain ⟨K, hKi, γ, rfl⟩ :=
    integralCompactlySupportedCohomologyOn_exists_representative n (U i) (hU i) β
  rw [integralRelativeToCompactlySupportedCohomologyOn_pushforward n (U i) (hU i)] at hβ
  obtain ⟨L, hKL, hLγ⟩ :=
    (integralRelativeToCompactlySupportedCohomology_eq_zero_iff n K γ).mp hβ
  obtain ⟨j, hLj⟩ := L.isCompact.elim_directed_cover U hU
    (by rw [hcover]; exact _root_.Set.subset_univ _) hdir
  obtain ⟨l, hil, hjl⟩ := hdir i j
  refine ⟨l, hil, ?_⟩
  rw [integralRelativeToCompactlySupportedCohomologyOn_inclusion n (U i) (U l) hil
    ((hU i).preimage continuous_subtype_val)]
  exact (integralRelativeToCompactlySupportedCohomologyOn_eq_zero_iff n (U l) (hU l)
    K (hKi.trans hil) γ).mpr ⟨L, hLj.trans hjl, hKL, hLγ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_eq_zero_of_directed_open_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_eq_zero_of_directed_open_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_eq_zero_of_directed_open_cover ``Submission.DifferentialGeometry.Topology.integralCompactlySupportedCohomologyPushforward_eq_zero_of_directed_open_cover

end DifferentialGeometry.Topology

end
