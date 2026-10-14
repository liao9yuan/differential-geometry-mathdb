/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Manifold.BicollarComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

universe u

def IsBicollared {X : Type u} [TopologicalSpace X] (S : Set X) : Prop :=
  Nonempty (ThreeManifold.TwoSidedCollar (Subtype.val : S → X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsBicollared then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsBicollared"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsBicollared ``Submission.DifferentialGeometry.Topology.IsBicollared

theorem isBicollared_iff_exists_isOpenEmbedding {X : Type u} [TopologicalSpace X]
    (S : Set X) :
    IsBicollared S ↔
      ∃ Φ : S × ℝ → X, Topology.IsOpenEmbedding Φ ∧ ∀ x : S, Φ (x, 0) = (x : X) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.toFun, h.isOpenEmbedding_toFun, h.zero_eq⟩
  · rintro ⟨Φ, hΦ, hzero⟩
    exact ⟨⟨Φ, hΦ, hzero⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isBicollared_iff_exists_isOpenEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isBicollared_iff_exists_isOpenEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isBicollared_iff_exists_isOpenEmbedding ``Submission.DifferentialGeometry.Topology.isBicollared_iff_exists_isOpenEmbedding

theorem compl_frontier_eq_interior_union_compl {X : Type u} [TopologicalSpace X]
    {C : Set X} (hC : IsClosed C) : (frontier C)ᶜ = interior C ∪ Cᶜ := by
  ext x
  rw [hC.frontier_eq]
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · exact Or.inl (by by_contra hni; exact hx ⟨hxC, hni⟩)
    · exact Or.inr hxC
  · rintro (hx | hx) hmem
    · exact hmem.2 hx
    · exact hx hmem.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compl_frontier_eq_interior_union_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compl_frontier_eq_interior_union_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compl_frontier_eq_interior_union_compl ``Submission.DifferentialGeometry.Topology.compl_frontier_eq_interior_union_compl

theorem compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier
    {X : Type u} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] {C : Set X} [Nonempty ↥(frontier C)]
    (hCclosed : IsClosed C)
    (hfrcompact : IsCompact (frontier C)) (hfrconn : IsConnected (frontier C))
    (hint : (interior C).Nonempty) (hcompl : Cᶜ.Nonempty)
    (h : ThreeManifold.TwoSidedCollar (Subtype.val : frontier C → X)) :
    Cᶜ = h.negativeSide ∨ Cᶜ = h.positiveSide := by
  have _ : CompactSpace ↥(frontier C) := isCompact_iff_compactSpace.mp hfrcompact
  have _ : ConnectedSpace ↥(frontier C) := isConnected_iff_connectedSpace.mp hfrconn
  have hcomplement : h.complement = (frontier C)ᶜ := by
    change (Set.range (Subtype.val : frontier C → X))ᶜ = (frontier C)ᶜ
    rw [Subtype.range_coe]
  have hkey : (frontier C)ᶜ = h.negativeSide ∪ h.positiveSide := by
    rw [← hcomplement]
    exact h.complement_eq_negativeSide_union_positiveSide
  have hIunion : (frontier C)ᶜ = interior C ∪ Cᶜ :=
    compl_frontier_eq_interior_union_compl hCclosed
  have hsets : interior C ∪ Cᶜ = h.negativeSide ∪ h.positiveSide := by
    rw [← hIunion, ← hkey]
  have hdisj : Disjoint (interior C) Cᶜ := disjoint_compl_right.mono_left interior_subset
  have hNsub : h.negativeSide ⊆ interior C ∪ Cᶜ := by
    rw [hsets]; exact _root_.Set.subset_union_left
  have hPsub : h.positiveSide ⊆ interior C ∪ Cᶜ := by
    rw [hsets]; exact _root_.Set.subset_union_right
  have hNcase := (h.isConnected_negativeSide).isPreconnected.subset_or_subset
    isOpen_interior hCclosed.isOpen_compl hdisj hNsub
  have hPcase := (h.isConnected_positiveSide).isPreconnected.subset_or_subset
    isOpen_interior hCclosed.isOpen_compl hdisj hPsub
  rcases hNcase with hN | hN
  · rcases hPcase with hP | hP
    · obtain ⟨x, hx⟩ := hcompl
      have hxmem : x ∈ h.negativeSide ∪ h.positiveSide := by
        rw [← hsets]; exact Or.inr hx
      rcases hxmem with hxm | hxm
      · exact absurd hx (Set.disjoint_left.mp hdisj (hN hxm))
      · exact absurd hx (Set.disjoint_left.mp hdisj (hP hxm))
    · refine Or.inr (Subset.antisymm (fun x hx => ?_) hP)
      have hxmem : x ∈ h.negativeSide ∪ h.positiveSide := by
        rw [← hsets]; exact Or.inr hx
      rcases hxmem with hxm | hxm
      · exact absurd hx (Set.disjoint_left.mp hdisj (hN hxm))
      · exact hxm
  · rcases hPcase with hP | hP
    · refine Or.inl (Subset.antisymm (fun x hx => ?_) hN)
      have hxmem : x ∈ h.negativeSide ∪ h.positiveSide := by
        rw [← hsets]; exact Or.inr hx
      rcases hxmem with hxm | hxm
      · exact hxm
      · exact absurd hx (Set.disjoint_left.mp hdisj (hP hxm))
    · obtain ⟨x, hx⟩ := hint
      have hxmem : x ∈ h.negativeSide ∪ h.positiveSide := by
        rw [← hsets]; exact Or.inl hx
      rcases hxmem with hxm | hxm
      · exact absurd (hN hxm) (Set.disjoint_left.mp hdisj hx)
      · exact absurd (hP hxm) (Set.disjoint_left.mp hdisj hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier ``Submission.DifferentialGeometry.Topology.compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier

theorem isConnected_compl_of_isBicollared_frontier {X : Type u} [TopologicalSpace X]
    [T2Space X] [ConnectedSpace X] [LocallyPathConnectedSpace X] {C : Set X}
    (hCclosed : IsClosed C) (hfrcompact : IsCompact (frontier C))
    (hfrconn : IsConnected (frontier C)) (hint : (interior C).Nonempty)
    (hcompl : Cᶜ.Nonempty) (hbi : IsBicollared (frontier C)) :
    IsConnected Cᶜ := by
  obtain ⟨h⟩ := hbi
  have _ : Nonempty ↥(frontier C) := hfrconn.nonempty.to_subtype
  rcases compl_eq_negativeSide_or_positiveSide_of_isBicollared_frontier
    hCclosed hfrcompact hfrconn hint hcompl h with hC | hC
  · rw [hC]; exact h.isConnected_negativeSide
  · rw [hC]; exact h.isConnected_positiveSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isConnected_compl_of_isBicollared_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isConnected_compl_of_isBicollared_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isConnected_compl_of_isBicollared_frontier ``Submission.DifferentialGeometry.Topology.isConnected_compl_of_isBicollared_frontier

end DifferentialGeometry.Topology
