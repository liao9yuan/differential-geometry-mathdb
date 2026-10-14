/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronPush
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexFacetComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_sphere_disk_to_simplex
    {S D : Set E} (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    ∃ (T : Finset (EuclideanSpace ℝ (Fin 3))) (a : EuclideanSpace ℝ (Fin 3))
      (f : E → EuclideanSpace ℝ (Fin 3)),
      AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 3)) ∧ T.card = 4 ∧ a ∈ T ∧
      IsPLHomeomorphOn f S (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      f '' D = convexHull ℝ ((T.erase a : Finset (EuclideanSpace ℝ (Fin 3))) : Set _) := by
  classical
  obtain ⟨T, hT, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 2) (by simp) (0 : EuclideanSpace ℝ (Fin 3)) Filter.univ_mem
  have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hTcard)
    have hrange : _root_.Set.range ((↑) : T → EuclideanSpace ℝ (Fin 3)) =
        (T : Set (EuclideanSpace ℝ (Fin 3))) := Subtype.range_coe
    exact (congrArg (affineSpan ℝ) hrange).symm.trans h
  have hboundary : IsPLSphere 2 (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) :=
    isPLSphere_frontier_convexHull T hT hspan hTcard
  have hboundaryP := hboundary.isPolyhedron
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hboundary
  let g := v ∘ Function.invFunOn u (stdSimplexBoundary 3)
  have hg : IsPLHomeomorphOn g S (frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))) :=
    hu.symm.trans hv
  have hgD := hg.restrict hD.isPolyhedron hDS
  obtain ⟨a, ha, k, hk, hkC, hkD, -⟩ := exists_isPLHomeomorphOn_straighten_disk_in_tetrahedron
    T hT hTcard (hD.of_isPLHomeomorphOn hgD)
      ((_root_.Set.image_mono hDS).trans hg.image_eq.le) isOpen_univ (_root_.Set.subset_univ _)
  have hkfront : k '' frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) =
      frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3)))) := by
    rw [k.image_frontier, hkC]
  have hk' := hk.restrict hboundaryP (_root_.Set.subset_univ _)
  rw [hkfront] at hk'
  refine ⟨T, a, k ∘ g, hT, hTcard, ha, hg.trans hk', ?_⟩
  change (fun x => k (g x)) '' D = _
  rw [← _root_.Set.image_image k g]
  exact hkD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_sphere_disk_to_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_sphere_disk_to_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_sphere_disk_to_simplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_sphere_disk_to_simplex

theorem IsPLSphere.isPLBall_closure_sdiff {S D : Set E}
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    IsPLBall 2 (closure (S \ D)) := by
  classical
  obtain ⟨T, a, f, hT, hTcard, ha, hf, hfD⟩ :=
    exists_isPLHomeomorphOn_sphere_disk_to_simplex hS hD hDS
  let B := frontier (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 3))))
  let F : Set (EuclideanSpace ℝ (Fin 3)) :=
    convexHull ℝ (T.erase a : Set (EuclideanSpace ℝ (Fin 3)))
  have hF : IsPLBall 2 F := isPLBall_convexHull_of_affineIndependent (T.erase a)
    (affineIndependent_of_subset hT (Finset.erase_subset a T))
      (by rw [Finset.card_erase_of_mem ha, hTcard])
  have hFB : F ⊆ B := by
    change convexHull ℝ (T.erase a : Set (EuclideanSpace ℝ (Fin 3))) ⊆ B
    rw [← hfD]
    exact (_root_.Set.image_mono hDS).trans hf.image_eq.le
  obtain ⟨N, hN, hCN, -⟩ := exists_isPolyhedron_neighborhood
    (T.finite_toSet.isCompact_convexHull ℝ) isOpen_univ (_root_.Set.subset_univ _)
  have hFball := hF
  obtain ⟨q, hq⟩ := hF
  obtain ⟨k, hk, hkF, -⟩ := (hasPushProperty_convexHull_simplex T hT hTcard).2 F ⟨q, hq⟩ hFB
    |>.2.2.2 q hq N hN (sdiff_subset.trans hCN)
  have hcomp : IsPLBall 2 (closure (B \ F)) := by
    rw [← hkF]
    exact hFball.of_isPLHomeomorphOn
      (hk.restrict hFball.isPolyhedron (_root_.Set.subset_univ F))
  have himg : f '' closure (S \ D) = closure (B \ F) := by
    rw [hf.image_closure hS.isPolyhedron.isCompact _root_.Set.sdiff_subset,
      hf.bijOn.injOn.image_sdiff_subset hDS, hf.image_eq, hfD]
  have hsub : closure (S \ D) ⊆ S := closure_minimal _root_.Set.sdiff_subset hS.isPolyhedron.isClosed
  have hback : Function.invFunOn f S '' closure (B \ F) = closure (S \ D) := by
    rw [← himg, _root_.Set.image_image]
    have hInv : _root_.Set.EqOn (Function.invFunOn f S ∘ f) id (closure (S \ D)) :=
      fun x hx => hf.bijOn.invOn_invFunOn.1 (hsub hx)
    exact hInv.image_eq.trans (_root_.Set.image_id _)
  have hcompB : closure (B \ F) ⊆ B := closure_minimal _root_.Set.sdiff_subset isClosed_frontier
  have h := hcomp.of_isPLHomeomorphOn (hf.symm.restrict hcomp.isPolyhedron hcompB)
  rwa [hback] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isPLBall_closure_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isPLBall_closure_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isPLBall_closure_sdiff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isPLBall_closure_sdiff

theorem IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary {S D : Set E}
    (hS : IsPLSphere 2 S) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hDS : D ⊆ S) :
    D ∩ closure (S \ D) = q '' stdSimplexBoundary 2 := by
  classical
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  obtain ⟨T, a, f, hT, hTcard, ha, hf, hfD⟩ :=
    exists_isPLHomeomorphOn_sphere_disk_to_simplex hS hD hDS
  have hspan : affineSpan ℝ (T : Set (EuclideanSpace ℝ (Fin 3))) = ⊤ := by
    have h := hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hTcard)
    have hrange : _root_.Set.range ((↑) : T → EuclideanSpace ℝ (Fin 3)) =
        (T : Set (EuclideanSpace ℝ (Fin 3))) := Subtype.range_coe
    exact (congrArg (affineSpan ℝ) hrange).symm.trans h
  have hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  have hFcard : (T.erase a).card = 1 + 2 := by rw [Finset.card_erase_of_mem ha, hTcard]
  have hfDpl := hf.restrict hD.isPolyhedron hDS
  rw [hfD] at hfDpl
  have hJimage : f '' (q '' stdSimplexBoundary 2) = (simplexBoundary (T.erase a) hF).space := by
    rw [_root_.Set.image_image]
    exact image_stdSimplexBoundary_of_isPLHomeomorphOn_convexHull hF hFcard (hq.trans hfDpl)
  have hcl : closure (S \ D) ⊆ S := closure_minimal _root_.Set.sdiff_subset hS.isPolyhedron.isClosed
  have hJsub : q '' stdSimplexBoundary 2 ⊆ S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hDS (hq.bijOn.mapsTo hy.1)
  have himage : f '' (D ∩ closure (S \ D)) = f '' (q '' stdSimplexBoundary 2) := by
    rw [hf.bijOn.injOn.image_inter hDS hcl,
      hf.image_closure hS.isPolyhedron.isCompact _root_.Set.sdiff_subset,
      hf.bijOn.injOn.image_sdiff_subset hDS, hf.image_eq, hfD, hJimage]
    exact convexHull_erase_inter_closure_frontier_sdiff T hT hspan ha
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := himage ▸ (show f x ∈ f '' (D ∩ closure (S \ D)) from ⟨x, hx, rfl⟩)
    exact (hf.bijOn.injOn (hJsub hy) (hDS hx.1) hyx) ▸ hy
  · intro x hx
    obtain ⟨y, hy, hyx⟩ :=
      himage.symm ▸ (show f x ∈ f '' (q '' stdSimplexBoundary 2) from ⟨x, hx, rfl⟩)
    exact (hf.bijOn.injOn (hDS hy.1) (hJsub hx) hyx) ▸ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.inter_closure_sdiff_eq_image_stdSimplexBoundary

theorem IsPLSphere.closure_sdiff_eq_sdiff_image_stdSimplexBoundary {S D : Set E}
    (hS : IsPLSphere 2 S) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) (hDS : D ⊆ S) :
    closure (S \ D) = S \ (D \ q '' stdSimplexBoundary 2) := by
  have hJ := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS
  have hAS : closure (S \ D) ⊆ S := closure_minimal _root_.Set.sdiff_subset hS.isPolyhedron.isClosed
  ext x
  constructor
  · intro hx
    exact ⟨hAS hx, fun h => h.2 (hJ ▸ ⟨h.1, hx⟩)⟩
  · rintro ⟨hxS, hx⟩
    by_cases hxD : x ∈ D
    · have hxJ : x ∈ q '' stdSimplexBoundary 2 := not_not.mp (fun h => hx ⟨hxD, h⟩)
      exact (hJ.symm ▸ hxJ).2
    · exact subset_closure ⟨hxS, hxD⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_eq_sdiff_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_eq_sdiff_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_eq_sdiff_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_eq_sdiff_image_stdSimplexBoundary

theorem IsPLSphere.closure_sdiff_closure_sdiff_eq {S D : Set E}
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) :
    closure (S \ closure (S \ D)) = D := by
  obtain ⟨q, hq⟩ := hD
  have hJ := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS
  have heq : S \ closure (S \ D) = D \ q '' stdSimplexBoundary 2 := by
    rw [← hJ]
    ext x
    constructor
    · rintro ⟨hxS, hxA⟩
      have hxD : x ∈ D := by
        by_contra h
        exact hxA (subset_closure ⟨hxS, h⟩)
      exact ⟨hxD, fun h => hxA h.2⟩
    · rintro ⟨hxD, hxJ⟩
      exact ⟨hDS hxD, fun h => hxJ ⟨hxD, h⟩⟩
  rw [heq, hq.closure_sdiff_image_stdSimplexBoundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_closure_sdiff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_closure_sdiff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_closure_sdiff_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.closure_sdiff_closure_sdiff_eq

theorem IsPLSphere.image_stdSimplexBoundary_complement {S D : Set E}
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S)
    {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) (closure (S \ D))) :
    q '' stdSimplexBoundary 2 = closure (S \ D) ∩ D := by
  have hA : closure (S \ D) ⊆ S := closure_minimal _root_.Set.sdiff_subset hS.isPolyhedron.isClosed
  have h := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hA
  rw [hS.closure_sdiff_closure_sdiff_eq hD hDS] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.image_stdSimplexBoundary_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.image_stdSimplexBoundary_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.image_stdSimplexBoundary_complement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.image_stdSimplexBoundary_complement

theorem IsPLSphere.isConnected_sdiff_of_isPLBall_two {S D : Set E}
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) : IsConnected (S \ D) := by
  obtain ⟨q, hq⟩ := hS.isPLBall_closure_sdiff hD hDS
  have hJ := hS.image_stdSimplexBoundary_complement hD hDS hq
  have hA : closure (S \ D) ⊆ S := closure_minimal _root_.Set.sdiff_subset hS.isPolyhedron.isClosed
  have heq : closure (S \ D) \ q '' stdSimplexBoundary 2 = S \ D := by
    rw [hJ]
    ext x
    constructor
    · rintro ⟨hxA, hxJ⟩
      exact ⟨hA hxA, fun h => hxJ ⟨hxA, h⟩⟩
    · rintro ⟨hxS, hxD⟩
      exact ⟨subset_closure ⟨hxS, hxD⟩, fun h => hxD h.2⟩
  rw [← heq]
  exact hq.isConnected_sdiff_image_stdSimplexBoundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isConnected_sdiff_of_isPLBall_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isConnected_sdiff_of_isPLBall_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isConnected_sdiff_of_isPLBall_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isConnected_sdiff_of_isPLBall_two

end DifferentialGeometry.Topology.PiecewiseLinear
