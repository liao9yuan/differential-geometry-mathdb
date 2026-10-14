/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallGluingTwo
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDerivedNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellCone

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace IsCombinatorialManifoldWithBoundary

open _root_.Classical in
theorem isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s : Finset E} (hs : s ∈ K.faces) :
    IsCombinatorialManifoldWithBoundary 2 (derivedNeighborhoodCellBase K s) := by
  let c := s.centroid ℝ id
  have hc : ({c} : Finset E) ∈ (PiecewiseLinear.barycentricSubdivision K).faces :=
    singleton_centroid_mem_barycentricSubdivision K hs
  let _ : Finite
      (upperLink (PiecewiseLinear.barycentricSubdivision K) ({c} : Finset E)).faces :=
    (upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K) {c}).to_subtype
  rcases hK.barycentricSubdivision.isPLSphere_or_isPLBall_upperLink
      (PiecewiseLinear.barycentricSubdivision K) hc (k := 0) (Finset.card_singleton c)
      (Nat.zero_le 2) with
    hbase | hbase
  · exact hbase.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
  · exact hbase.isCombinatorialManifoldWithBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase

open _root_.Classical in
theorem isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {ι : Type*} {C : Set E}
    (hC : IsPLBall 2 C) (hCK : C ⊆ K.space)
    (d : Finset ι) (A : ι → Set E) (hA : ∀ i ∈ d, IsPLBall 2 (A i))
    (hAK : ∀ i ∈ d, A i ⊆ K.space) (hI : ∀ i ∈ d, IsPLBall 1 (C ∩ A i))
    (hdis : ∀ i ∈ d, ∀ j ∈ d, i ≠ j → Disjoint (A i) (A j)) :
    IsPLBall 2 (C ∪ ⋃ i ∈ d, A i) := by
  classical
  induction d using Finset.induction_on with
  | empty => simpa using hC
  | @insert i d hi ih =>
    have hA' : ∀ j ∈ d, IsPLBall 2 (A j) :=
      fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hAK' : ∀ j ∈ d, A j ⊆ K.space :=
      fun j hj => hAK j (Finset.mem_insert_of_mem hj)
    have hI' : ∀ j ∈ d, IsPLBall 1 (C ∩ A j) :=
      fun j hj => hI j (Finset.mem_insert_of_mem hj)
    have hdis' : ∀ j ∈ d, ∀ k ∈ d, j ≠ k → Disjoint (A j) (A k) :=
      fun j hj k hk hjk => hdis j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk) hjk
    have hprev := ih hA' hAK' hI' hdis'
    have hprevK : (C ∪ ⋃ j ∈ d, A j) ⊆ K.space :=
      _root_.Set.union_subset hCK (_root_.Set.iUnion₂_subset hAK')
    have hinter : (C ∪ ⋃ j ∈ d, A j) ∩ A i = C ∩ A i := by
      apply Subset.antisymm
      · rintro x ⟨hx | hx, hxi⟩
        · exact ⟨hx, hxi⟩
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
          exact ((hdis j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
            (ne_of_mem_of_not_mem hj hi)).le_bot ⟨hxj, hxi⟩).elim
      · rintro x ⟨hx, hxi⟩
        exact ⟨Or.inl hx, hxi⟩
    have h := hK.isPLBall_union_of_inter_isPLBall_one hprev
      (hA i (Finset.mem_insert_self _ _)) hprevK (hAK i (Finset.mem_insert_self _ _))
      (hinter.symm ▸ hI i (Finset.mem_insert_self _ _))
    simpa only [Finset.set_biUnion_insert, _root_.Set.union_assoc, _root_.Set.union_left_comm, _root_.Set.union_comm] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface

open _root_.Classical in
theorem isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ≠ t)
    (hcst : s ⊆ t ∨ t ⊆ s) (d : Finset (Finset E)) (hd : ∀ u ∈ d, u ∈ K.faces)
    (hne : ∀ u ∈ d, u ≠ s ∧ u ≠ t)
    (hcomp : ∀ u ∈ d, (s ⊆ u ∨ u ⊆ s) ∧ (t ⊆ u ∨ u ⊆ t))
    (hincomp : ∀ u ∈ d, ∀ v ∈ d, u ≠ v → ¬u ⊆ v ∧ ¬v ⊆ u) :
    IsPLBall 2 ((derivedNeighborhoodCell K s).space ∩
      ((derivedNeighborhoodCell K t).space ∪ ⋃ u ∈ d, (derivedNeighborhoodCell K u).space)) := by
  classical
  let _ : Finite (derivedNeighborhoodCellBase K s).faces :=
    (upperLink_faces_finite (PiecewiseLinear.barycentricSubdivision K)
      {s.centroid ℝ id}).to_subtype
  have hbase := hK.isCombinatorialManifoldWithBoundary_derivedNeighborhoodCellBase hs
  have hcenter := hK.isPLBall_derivedNeighborhoodCell_inter hs ht hst hcst
  let A := fun u => (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K u).space
  have hA (u : Finset E) (hu : u ∈ d) : IsPLBall 2 (A u) :=
    hK.isPLBall_derivedNeighborhoodCell_inter hs (hd u hu) (hne u hu).1.symm
      (hcomp u hu).1
  have hAB (u : Finset E) (hu : u ∈ d) :
      A u ⊆ (derivedNeighborhoodCellBase K s).space :=
    derivedNeighborhoodCell_inter_subset_base K hs (hd u hu) (hne u hu).1.symm
  have hcenterB :
      (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space ⊆
        (derivedNeighborhoodCellBase K s).space :=
    derivedNeighborhoodCell_inter_subset_base K hs ht hst
  have hI (u : Finset E) (hu : u ∈ d) :
      IsPLBall 1 (((derivedNeighborhoodCell K s).space ∩
        (derivedNeighborhoodCell K t).space) ∩ A u) := by
    have heq : ((derivedNeighborhoodCell K s).space ∩
        (derivedNeighborhoodCell K t).space) ∩ A u =
          (derivedNeighborhoodCell K s).space ∩
            (derivedNeighborhoodCell K t).space ∩ (derivedNeighborhoodCell K u).space := by
      ext x
      simp only [A, _root_.Set.mem_inter_iff]
      tauto
    rw [heq]
    exact hK.isPLBall_derivedNeighborhoodCell_inter_inter hs ht (hd u hu) hst
      (hne u hu).1.symm (hne u hu).2.symm hcst (hcomp u hu).1 (hcomp u hu).2
  have hdis (u : Finset E) (hu : u ∈ d) (v : Finset E) (hv : v ∈ d)
      (hneuv : u ≠ v) : Disjoint (A u) (A v) :=
    (disjoint_derivedNeighborhoodCell_space K (hd u hu) (hd v hv)
      (hincomp u hu v hv hneuv).1 (hincomp u hu v hv hneuv).2).mono
        _root_.Set.inter_subset_right _root_.Set.inter_subset_right
  have h := hbase.isPLBall_union_iUnion_of_pairwiseDisjoint_in_surface hcenter hcenterB
    d A hA hAB hI hdis
  simpa only [_root_.Set.inter_union_distrib_left, _root_.Set.inter_iUnion] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCell_inter_union_of_mem_faces

end IsCombinatorialManifoldWithBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
