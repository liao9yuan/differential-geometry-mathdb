/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Clopen

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

theorem IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary
    {Y T D : Set X} (hY : IsPreconnected Y) (hYT : Y ⊆ T) (hD : IsClosed D)
    (hYB : Disjoint Y (D ∩ closure (T \ D))) : Y ⊆ D ∨ Disjoint D Y := by
  have hcover : Y ⊆ D ∪ closure (T \ D) := fun x hx => by
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · exact Or.inr (subset_closure ⟨hYT hx, hxD⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (T \ D))
      hD isClosed_closure hcover hYB.inter_eq with h | h
  · exact Or.inl h
  · exact Or.inr (disjoint_left.mpr fun x hxD hxY =>
      disjoint_left.mp hYB hxY ⟨hxD, h hxY⟩)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.IsPreconnected
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary ``Submission.DifferentialGeometry.Topology.IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary

theorem subset_or_disjoint_of_pairwiseDisjoint_boundary
    {ι : Type*} {F : ι → Set X} {T D : Set X}
    (hF : ∀ i, IsPreconnected (F i)) (hFT : ∀ i, F i ⊆ T)
    (hdis : Pairwise fun i j => Disjoint (F i) (F j)) (hD : IsClosed D)
    (i₀ : ι) (hboundary : D ∩ closure (T \ D) = F i₀) :
    ∀ i, i ≠ i₀ → F i ⊆ D ∨ Disjoint D (F i) := by
  intro i hi
  exact IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary (hF i) (hFT i) hD
    (hboundary.symm ▸ hdis hi)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subset_or_disjoint_of_pairwiseDisjoint_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subset_or_disjoint_of_pairwiseDisjoint_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subset_or_disjoint_of_pairwiseDisjoint_boundary ``Submission.DifferentialGeometry.Topology.subset_or_disjoint_of_pairwiseDisjoint_boundary

end DifferentialGeometry.Topology
