/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSurfaceTrace
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallPairModel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) (hsA : s ∉ A.faces) :
    Disjoint (derivedNeighborhoodCell K s).space A.space := by
  rw [_root_.Set.disjoint_left]
  intro x hx hxA
  have hxAb : x ∈ (barycentricSubdivision A).space :=
    (barycentricSubdivision_isSubdivision A).space_eq.symm ▸ hxA
  obtain ⟨t, ht, hxt⟩ := (barycentricSubdivision A).mem_space_iff.mp hxAb
  have hsub := subset_of_mem_dualCell_of_mem_convexHull (barycentricSubdivision K)
    (singleton_centroid_mem_barycentricSubdivision K hs)
    (barycentricSubdivision_faces_subset hAK ht)
    (by rwa [derivedNeighborhoodCell_eq_dualCell K hs] at hx) hxt
  have hcA : s.centroid ℝ id ∈ A.space := by
    rw [← (barycentricSubdivision_isSubdivision A).space_eq]
    exact (barycentricSubdivision A).subset_space ht
      (hsub (Finset.mem_singleton_self _))
  exact hsA (mem_faces_of_mem_openSimplex_of_mem_space hAK hs
    (centroid_mem_openSimplex_of_mem_faces K s hs) hcA)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem

open _root_.Classical in
theorem derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton
    (K Γ A : Geometry.SimplicialComplex ℝ E)
    (hΓK : Γ.faces ⊆ K.faces) (hAK : A.faces ⊆ K.faces)
    {p : E} (hp : {p} ∈ K.faces) (hAΓ : A.space ∩ Γ.space = {p})
    {t : Finset E} (ht : t ∈ Γ.faces) (htp : t ≠ {p}) :
    Disjoint (derivedNeighborhoodCell K t).space A.space := by
  apply derivedNeighborhoodCell_disjoint_subcomplex_of_not_mem K A hAK (hΓK ht)
  intro htA
  have hc : t.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    t.centroid_mem_convexHull (Γ.nonempty_of_mem_faces ht)
  have hcp : t.centroid ℝ id = p := hAΓ.subset
    ⟨A.convexHull_subset_space htA hc, Γ.convexHull_subset_space ht hc⟩
  apply centroid_ne_centroid_of_ne K (hΓK ht) hp htp
  simpa only [Finset.centroid_singleton, id_eq] using hcp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_disjoint_of_subcomplex_inter_singleton

open _root_.Classical in
theorem derivedNeighborhoodCell_inter_eq_segment_of_base_inter_singleton
    (K A : Geometry.SimplicialComplex ℝ E) (hAK : A.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ A.faces) {x : E}
    (hx : (derivedNeighborhoodCellBase K s).space ∩ A.space = {x}) :
    (derivedNeighborhoodCell K s).space ∩ A.space = segment ℝ (s.centroid ℝ id) x := by
  have hbase : (derivedNeighborhoodCellBase A s).space = {x} :=
    (derivedNeighborhoodCellBase_inter_subcomplex K A hAK hs).symm.trans hx
  rw [derivedNeighborhoodCell_inter_subcomplex K A hAK hs,
    derivedNeighborhoodCell_space_eq_coneSet A hs]
  change coneSet (s.centroid ℝ id) (derivedNeighborhoodCellBase A s).space = _
  rw [hbase, coneSet_eq_iUnion_segment (_root_.Set.singleton_nonempty x), _root_.Set.biUnion_singleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_eq_segment_of_base_inter_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_eq_segment_of_base_inter_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_eq_segment_of_base_inter_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCell_inter_eq_segment_of_base_inter_singleton

open _root_.Classical in
theorem boundaryComplex_space_of_parametrized_Icc [FiniteDimensional ℝ E]
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc a b) A.space) :
    (boundaryComplex 1 A).space = {γ a, γ b} := by
  obtain ⟨I, hIfin, hIsp⟩ :=
    (isHPolytope_Icc (a := a) (b := b)).isPolyhedron.exists_simplicialComplex
  let _ : Finite I.faces := hIfin.to_subtype
  have hI : IsCombinatorialManifoldWithBoundary 1 I :=
    (hIsp.symm ▸ isPLBall_Icc hab).isCombinatorialManifoldWithBoundary
  have hγI : IsPLHomeomorphOn γ I.space A.space := hIsp.symm ▸ hγ
  rw [boundaryComplex_space_of_isPLHomeomorphOn I A hI hγI,
    ← frontier_space_eq_boundaryComplex_space_of_finrank (n := 0) (by simp) I hI,
    hIsp, frontier_Icc hab.le, _root_.Set.image_pair]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_parametrized_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_parametrized_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_parametrized_Icc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_parametrized_Icc

open _root_.Classical in
theorem exists_derived_interval_link_parameter [FiniteDimensional ℝ E]
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hAK : A.faces ⊆ K.faces)
    {γ : ℝ → E} {a b : ℝ} (hab : a < b) (hγ : IsPLHomeomorphOn γ (_root_.Set.Icc a b) A.space)
    {p : E} (hp : {p} ∈ K.faces) (hpγ : p = γ a ∨ p = γ b) :
    ∃ t ∈ _root_.Set.Icc a b, γ t ≠ p ∧
      (derivedNeighborhoodCellBase K {p}).space ∩ A.space = {γ t} := by
  have hpbd : p ∈ (boundaryComplex 1 A).space := by
    rw [boundaryComplex_space_of_parametrized_Icc A hab hγ]
    exact hpγ
  have hpA : {p} ∈ A.faces := mem_faces_of_mem_openSimplex_of_mem_space hAK hp
    (by simpa only [Finset.centroid_singleton, id_eq] using
      centroid_mem_openSimplex (Finset.singleton_nonempty p))
    (boundaryComplex_space_subset 1 A hpbd)
  have hpB : {p} ∈ (boundaryComplex 1 A).faces :=
    mem_faces_of_mem_openSimplex_of_mem_space (boundaryComplex_faces_subset 1 A) hpA
      (by simpa only [Finset.centroid_singleton, id_eq] using
        centroid_mem_openSimplex (Finset.singleton_nonempty p)) hpbd
  have hA : IsCombinatorialManifoldWithBoundary 1 A :=
    ((isPLBall_Icc hab).of_isPLHomeomorphOn hγ).isCombinatorialManifoldWithBoundary
  obtain ⟨x, hx⟩ := isPLBall_zero_iff.mp
    (hA.isPLBall_derivedNeighborhoodCellBase_inter K A hAK hpB)
  have hxmem : x ∈ (derivedNeighborhoodCellBase K {p}).space ∩ A.space :=
    hx.symm ▸ _root_.Set.mem_singleton x
  have hxp : x ≠ p := by
    intro hxp
    have hcone := isConeBase_centroid_upperLink K hp
    have hpbase : p ∉ (derivedNeighborhoodCellBase K {p}).space := by
      simpa only [derivedNeighborhoodCellBase, Finset.centroid_singleton, id_eq] using
        hcone.notMem_space
    exact hpbase (hxp ▸ hxmem.1)
  obtain ⟨t, ht, htx⟩ := hγ.bijOn.surjOn hxmem.2
  exact ⟨t, ht, fun h => hxp (htx.symm.trans h), hx.trans (congrArg _root_.Singleton.singleton htx.symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_derived_interval_link_parameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_derived_interval_link_parameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_derived_interval_link_parameter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_derived_interval_link_parameter

end DifferentialGeometry.Topology.PiecewiseLinear
