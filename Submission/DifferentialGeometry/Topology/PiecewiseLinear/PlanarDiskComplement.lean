/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.eq_of_subset_of_frontier_subset
    {C D : Set (EuclideanSpace ℝ (Fin 2))} (hC : IsPLBall 2 C) (hD : IsPLBall 2 D)
    (hCD : C ⊆ D) (hbd : frontier D ⊆ C) : C = D := by
  have hsub : frontier D ⊆ frontier C := fun x hx =>
    ⟨subset_closure (hbd hx), fun hxi => hx.2 (interior_mono hCD hxi)⟩
  have heq := PlanarJordan.eq_of_isJordanCurve_of_subset
    (isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier)
    (isJordanCurve_of_isPLSphere_one hC.isPLSphere_frontier) hsub
  rw [← hC.closure_interior, ← hD.closure_interior,
    hC.interior_eq_inside_frontier, hD.interior_eq_inside_frontier, heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.eq_of_subset_of_frontier_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.eq_of_subset_of_frontier_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.eq_of_subset_of_frontier_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.eq_of_subset_of_frontier_subset

theorem IsPLBall.isPLBall_closure_sdiff_of_boundary_arc
    {C D : Set (EuclideanSpace ℝ (Fin 2))} (hD : IsPLBall 2 D) (hC : IsPLBall 2 C)
    (hCD : C ⊆ D) (hI : IsPLBall 1 (C ∩ frontier D)) :
    IsPLBall 2 (closure (D \ C)) := by
  let I := C ∩ frontier D
  obtain ⟨p, q, hIpq⟩ := hI.isArc.exists_isArcBetween
  have hIC : I ⊆ frontier C := fun x hx =>
    ⟨subset_closure hx.1, fun hxi => hx.2.2 (interior_mono hCD hxi)⟩
  obtain ⟨A, hcutC, _, hA⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hC.isPLSphere_frontier hIpq hIC
  obtain ⟨B, hcutD, _, _⟩ :=
    exists_isCutPair_of_isArcBetween_subset_isPLSphere hD.isPLSphere_frontier hIpq
        _root_.Set.inter_subset_right
  have hcross : Schoenflies.IsCrosscut (frontier D) A p q := by
    refine ⟨isJordanCurve_of_isPLSphere_one hD.isPLSphere_frontier, hcutC.snd,
      hA.isPolyhedron.isPolygonal_of_isArcBetween hcutC.snd,
      hIpq.left_mem.2, hIpq.right_mem.2, ?_⟩
    rw [← hD.interior_eq_inside_frontier]
    intro x hx
    have hxC : x ∈ C := hC.isPolyhedron.isClosed.frontier_subset (hcutC.snd_subset hx.1)
    apply (mem_interior_iff_notMem_frontier (hCD hxC)).mpr
    intro hxD
    have hxI : x ∈ I := ⟨hxC, hxD⟩
    exact hx.2 (hcutC.inter_eq ▸ ⟨hxI, hx.1⟩)
  have hS := isPLSphere_one_union_of_isCrosscut hD.isPLSphere_frontier hA hcross hcutD.symm
  let V := closure (Schoenflies.inside (B ∪ A))
  have hV : IsPLBall 2 V := isPLBall_closure_inside_of_isPLSphere_one hS
  have hfV : frontier V = B ∪ A := frontier_closure_inside_of_isPLSphere_one hS
  have hCeq : closure (Schoenflies.inside (I ∪ A)) = C := by
    rw [hcutC.union_eq, ← hC.interior_eq_inside_frontier, hC.closure_interior]
  have hunion : C ∪ V = D := by
    rw [← hCeq]
    exact (PlanarJordan.closure_inside_union_of_isCrosscut hcross hcutD).trans (by
      rw [← hD.interior_eq_inside_frontier, hD.closure_interior])
  have hinter : C ∩ V = A := by
    rw [← hCeq]
    exact PlanarJordan.closure_inside_inter_of_isCrosscut hcross hcutD
  have heq : closure (D \ C) = V := by
    apply Subset.antisymm
    · apply closure_minimal ?_ hV.isPolyhedron.isClosed
      rintro x ⟨hxD, hxC⟩
      exact (hunion.symm ▸ hxD).resolve_left hxC
    · rw [← hV.closure_interior]
      apply closure_mono
      intro x hxV
      refine ⟨hunion ▸ Or.inr (interior_subset hxV), ?_⟩
      intro hxC
      have hxA : x ∈ A := hinter ▸ ⟨hxC, interior_subset hxV⟩
      have hxf : x ∈ frontier V := hfV.symm ▸ Or.inr hxA
      exact hxf.2 hxV
  rwa [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isPLBall_closure_sdiff_of_boundary_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isPLBall_closure_sdiff_of_boundary_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isPLBall_closure_sdiff_of_boundary_arc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isPLBall_closure_sdiff_of_boundary_arc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem isPLBall_closure_sdiff_of_inter_boundaryComplex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {C : Set E} (hC : IsPLBall 2 C) (hCK : C ⊆ K.space)
    (hI : IsPLBall 1 (C ∩ (boundaryComplex 2 K).space)) :
    IsPLBall 2 (closure (K.space \ C)) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  obtain ⟨R, _, hRfin, _, hR, _⟩ := exists_isPLBall_pair_with_segment_inter
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨f, hf⟩ := hK
  obtain ⟨g, hg⟩ := hR
  have hK : IsPLBall 2 K.space := ⟨f, hf⟩
  have hR : IsPLBall 2 R.space := ⟨g, hg⟩
  let u := g ∘ Function.invFunOn f (stdSimplex ℝ (Fin 3))
  have hu : IsPLHomeomorphOn u K.space R.space := hf.symm.trans hg
  have hC' := hC.of_isPLHomeomorphOn (hu.restrict hC.isPolyhedron hCK)
  have hbd : u '' (boundaryComplex 2 K).space = frontier R.space := by
    rw [← boundaryComplex_space_of_isPLHomeomorphOn K R hK.isCombinatorialManifoldWithBoundary hu,
      ← frontier_space_eq_boundaryComplex_space hR.isCombinatorialManifoldWithBoundary]
  have hI' : IsPLBall 1 (u '' C ∩ frontier R.space) := by
    rw [← hbd, ← hu.bijOn.injOn.image_inter hCK (boundaryComplex_space_subset 2 K)]
    exact hI.of_isPLHomeomorphOn (hu.restrict hI.isPolyhedron (inter_subset_left.trans hCK))
  have hcomp := hR.isPLBall_closure_sdiff_of_boundary_arc hC'
    ((_root_.Set.image_mono hCK).trans hu.image_eq.le) hI'
  have himage : u '' closure (K.space \ C) = closure (R.space \ u '' C) := by
    rw [hu.image_closure hK.isPolyhedron.isCompact _root_.Set.sdiff_subset,
      hu.bijOn.injOn.image_sdiff_subset hCK, hu.image_eq]
  have hpoly := hK.isPolyhedron.closure_sdiff hC.isPolyhedron
  have hsub : closure (K.space \ C) ⊆ K.space :=
    closure_minimal _root_.Set.sdiff_subset hK.isPolyhedron.isClosed
  rw [← himage] at hcomp
  exact hcomp.of_isPLHomeomorphOn (hu.restrict hpoly hsub).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_sdiff_of_inter_boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_sdiff_of_inter_boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_sdiff_of_inter_boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_sdiff_of_inter_boundaryComplex

open _root_.Classical in
theorem eq_of_isPLBall_of_boundaryComplex_subset
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {C : Set E} (hC : IsPLBall 2 C) (hCK : C ⊆ K.space)
    (hbd : (boundaryComplex 2 K).space ⊆ C) : C = K.space := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 2)) := Classical.decEq _
  obtain ⟨R, _, hRfin, _, hR, _⟩ := exists_isPLBall_pair_with_segment_inter
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨f, hf⟩ := hK
  obtain ⟨g, hg⟩ := hR
  have hK : IsPLBall 2 K.space := ⟨f, hf⟩
  have hR : IsPLBall 2 R.space := ⟨g, hg⟩
  let u := g ∘ Function.invFunOn f (stdSimplex ℝ (Fin 3))
  have hu : IsPLHomeomorphOn u K.space R.space := hf.symm.trans hg
  have hC' := hC.of_isPLHomeomorphOn (hu.restrict hC.isPolyhedron hCK)
  have hbd' : frontier R.space ⊆ u '' C := by
    rw [frontier_space_eq_boundaryComplex_space hR.isCombinatorialManifoldWithBoundary,
      boundaryComplex_space_of_isPLHomeomorphOn K R hK.isCombinatorialManifoldWithBoundary hu]
    exact _root_.Set.image_mono hbd
  have heq := hC'.eq_of_subset_of_frontier_subset hR
    ((_root_.Set.image_mono hCK).trans hu.image_eq.le) hbd'
  exact (hu.bijOn.injOn.image_eq_image_iff hCK Subset.rfl).mp (heq.trans hu.image_eq.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_isPLBall_of_boundaryComplex_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_of_isPLBall_of_boundaryComplex_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_isPLBall_of_boundaryComplex_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_of_isPLBall_of_boundaryComplex_subset
end DifferentialGeometry.Topology.PiecewiseLinear
