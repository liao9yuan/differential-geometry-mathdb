import Submission.DifferentialGeometry.Topology.SphereSeparation.Sides

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Topology.SphereSeparation

open _root_.Set

namespace SphereSides

variable {X : Type*} [TopologicalSpace X] {S U V O : Set X}

theorem neighborhood_halves_opposite_of_inter_nonempty (d : SphereSides S)
    (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ Sᶜ) (hVS : V ⊆ Sᶜ)
    (hOopen : IsOpen O) (hSO : (S ∩ O).Nonempty) (hO : O ⊆ (U ∪ S) ∪ V) :
    Xor (U ⊆ d.compactSide ∧ V ⊆ d.endSide)
      (U ⊆ d.endSide ∧ V ⊆ d.compactSide) := by
  have not_both_compact :
      ¬ (U ⊆ d.compactSide ∧ V ⊆ d.compactSide) := by
    rintro ⟨hUB, hVB⟩
    obtain ⟨s, hsS, hsO⟩ := hSO
    have hsClosure : s ∈ closure d.endSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_endSide] using hsS
    obtain ⟨x, hxO, hxE⟩ := mem_closure_iff.1 hsClosure O hOopen hsO
    rcases hO hxO with (hxU | hxS) | hxV
    · exact Set.disjoint_left.1 d.disjoint (hUB hxU) hxE
    · exact Set.disjoint_left.1 d.endSide_disjoint_sphere hxE hxS
    · exact Set.disjoint_left.1 d.disjoint (hVB hxV) hxE
  have not_both_end : ¬ (U ⊆ d.endSide ∧ V ⊆ d.endSide) := by
    rintro ⟨hUE, hVE⟩
    obtain ⟨s, hsS, hsO⟩ := hSO
    have hsClosure : s ∈ closure d.compactSide := by
      apply frontier_subset_closure
      simpa only [d.frontier_compactSide] using hsS
    obtain ⟨x, hxO, hxB⟩ := mem_closure_iff.1 hsClosure O hOopen hsO
    rcases hO hxO with (hxU | hxS) | hxV
    · exact Set.disjoint_left.1 d.disjoint hxB (hUE hxU)
    · exact Set.disjoint_left.1 d.compactSide_disjoint_sphere hxB hxS
    · exact Set.disjoint_left.1 d.disjoint hxB (hVE hxV)
  rcases d.subset_compactSide_or_subset_endSide hU.isPreconnected hUS with hUB | hUE
  · rcases d.subset_compactSide_or_subset_endSide hV.isPreconnected hVS with hVB | hVE
    · exact False.elim (not_both_compact ⟨hUB, hVB⟩)
    · refine Or.inl ⟨⟨hUB, hVE⟩, ?_⟩
      rintro ⟨hUE', _⟩
      obtain ⟨x, hxU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB hxU) (hUE' hxU)
  · rcases d.subset_compactSide_or_subset_endSide hV.isPreconnected hVS with hVB | hVE
    · refine Or.inr ⟨⟨hUE, hVB⟩, ?_⟩
      rintro ⟨hUB', _⟩
      obtain ⟨x, hxU⟩ := hU.nonempty
      exact Set.disjoint_left.1 d.disjoint (hUB' hxU) (hUE hxU)
    · exact False.elim (not_both_end ⟨hUE, hVE⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite_of_inter_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite_of_inter_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite_of_inter_nonempty ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite_of_inter_nonempty

theorem neighborhood_halves_opposite (d : SphereSides S)
    (hS : S.Nonempty) (hU : IsConnected U) (hV : IsConnected V)
    (hUS : U ⊆ Sᶜ) (hVS : V ⊆ Sᶜ)
    (hOopen : IsOpen O) (hSO : S ⊆ O) (hO : O ⊆ (U ∪ S) ∪ V) :
    Xor (U ⊆ d.compactSide ∧ V ⊆ d.endSide)
      (U ⊆ d.endSide ∧ V ⊆ d.compactSide) := by
  exact d.neighborhood_halves_opposite_of_inter_nonempty hU hV hUS hVS hOopen
    (hS.mono (fun _ hx => ⟨hx, hSO hx⟩)) hO

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite ``Submission.DifferentialGeometry.Topology.SphereSeparation.SphereSides.neighborhood_halves_opposite

end SphereSides

end DifferentialGeometry.Topology.SphereSeparation
