/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCellBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem derivedNeighborhoodCell_inter_derivedNeighborhood_eq_iUnion
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsL : s ∉ L.faces)
    (hcard : ∀ t ∈ L.faces, t.card ≤ s.card)
    (hproper : ∀ t : Finset E, t.Nonempty → t ⊂ s → t ∈ L.faces) :
    (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhood K L).space =
      ⋃ t ∈ (simplexBoundary s (K.indep hs)).faces,
        (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space := by
  classical
  rw [← iUnion_derivedNeighborhoodCell_space K L hLK]
  apply Subset.antisymm
  · rintro x ⟨hxs, hxL⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxL
    have hne : t ≠ s := fun h => hsL (h ▸ ht)
    have hts : t ⊆ s := by
      rcases subset_or_subset_of_nonempty_derivedNeighborhoodCell_inter K
        (hLK ht) hs ⟨x, hxt, hxs⟩ with h | h
      · exact h
      · exact (hne (Finset.eq_of_subset_of_card_le h (hcard t ht)).symm).elim
    exact mem_iUnion₂.mpr
      ⟨t, ⟨hts, L.nonempty_of_mem_faces ht, hne⟩, hxs, hxt⟩
  · intro x hx
    obtain ⟨t, ht, hxs, hxt⟩ := mem_iUnion₂.mp hx
    exact ⟨hxs, mem_iUnion₂.mpr
      ⟨t, hproper t ht.2.1 (Finset.ssubset_iff_subset_ne.mpr ⟨ht.1, ht.2.2⟩), hxt⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_derivedNeighborhood_eq_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_derivedNeighborhood_eq_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_derivedNeighborhood_eq_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_derivedNeighborhood_eq_iUnion

open _root_.Classical in
theorem boundaryComplex_derivedNeighborhoodCell_space
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifold (n + 2) K)
    {s : Finset E} (hs : s ∈ K.faces) :
    (boundaryComplex (n + 2) (derivedNeighborhoodCell K s)).space =
      (derivedNeighborhoodCell K s).space ∩
        ⋃ t ∈ K.faces \ {s}, (derivedNeighborhoodCell K t).space := by
  classical
  let C := derivedNeighborhoodCell K s
  let R := ⋃ t ∈ K.faces \ {s}, (derivedNeighborhoodCell K t).space
  let _ : Finite C.faces := (derivedNeighborhoodCell_faces_finite K s).to_subtype
  have hKw := hK.isCombinatorialManifoldWithBoundary
  have hC := hKw.isPLBall_derivedNeighborhoodCell hs
  have hfin : (K.faces \ {s}).Finite := (Set.toFinite K.faces).subset _root_.Set.sdiff_subset
  have hclosed : IsClosed R := hfin.isClosed_biUnion fun t ht =>
    (hKw.isPLBall_derivedNeighborhoodCell ht.1).isPolyhedron.isClosed
  have hsub : (secondDerived K).space \ C.space ⊆ R := by
    rintro x ⟨hxK, hxC⟩
    have hxK' : x ∈ K.space := (secondDerived_isSubdivision K).space_eq ▸ hxK
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp
      (space_subset_iUnion_derivedNeighborhoodCell_space K K Subset.rfl hxK')
    have hne : t ≠ s := fun h =>
      hxC (show x ∈ (derivedNeighborhoodCell K s).space from h ▸ hxt)
    exact mem_iUnion₂.mpr ⟨t, ⟨ht, hne⟩, hxt⟩
  have hboundary : (boundaryComplex (n + 2) C).space ⊆ R :=
    (boundaryComplex_space_subset_closure_sdiff_of_isCombinatorialManifold
      (secondDerived K) C (hK.of_isSubdivision (secondDerived_isSubdivision K))
      hC.isCombinatorialManifoldWithBoundary (derivedNeighborhoodCell_faces_subset K s)).trans
        (closure_minimal hsub hclosed)
  apply Subset.antisymm
  · exact _root_.Set.subset_inter (boundaryComplex_space_subset (n + 2) C) hboundary
  · rintro x ⟨hxs, hxR⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxR
    exact hKw.derivedNeighborhoodCell_inter_subset_boundaryComplex hs ht.1
        (fun h => ht.2 h.symm) ⟨hxs, hxt⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_derivedNeighborhoodCell_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_derivedNeighborhoodCell_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_derivedNeighborhoodCell_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_derivedNeighborhoodCell_space

end DifferentialGeometry.Topology.PiecewiseLinear
