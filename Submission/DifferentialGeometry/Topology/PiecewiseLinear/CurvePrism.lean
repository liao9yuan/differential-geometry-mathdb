/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Prism
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem boundaryComplex_space_prism_one [d : DecidableEq (E × ℝ)]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLBall 1 K.space) {a b : ℝ} (hab : a < b)
    (A : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite A.faces]
    (hAspace : A.space = K.space ×ˢ _root_.Set.Icc a b) :
    (boundaryComplex 2 A).space =
      K.space ×ˢ {a, b} ∪ (boundaryComplex 1 K).space ×ˢ _root_.Set.Icc a b := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  let _ : DecidableEq ℝ := Classical.decEq _
  let _ : DecidableEq (ℝ × ℝ) := Classical.decEq _
  obtain ⟨T, hTfin, hTspace⟩ :=
    (isPLBall_Icc zero_lt_one).isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT : IsPLBall 1 T.space := hTspace.symm ▸ isPLBall_Icc zero_lt_one
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hK
  have hfT : IsPLHomeomorphOn f T.space K.space := hTspace.symm ▸ hf
  have hprod := isPLBall_two_prod hT (isPLBall_Icc hab)
  obtain ⟨R, hRfin, hRspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hR : IsPLBall 2 R.space := hRspace.symm ▸ hprod
  have hboundary : (boundaryComplex 2 R).space =
      T.space ×ˢ {a, b} ∪ (boundaryComplex 1 T).space ×ˢ _root_.Set.Icc a b := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank
      (by simp [Module.finrank_prod]) R hR.isCombinatorialManifoldWithBoundary,
      hRspace, frontier_prod_eq, (isPolyhedron_space T).isClosed.closure_eq,
      frontier_Icc hab.le, isClosed_Icc.closure_eq,
      frontier_space_eq_boundaryComplex_space_of_finrank (by simp) T
        hT.isCombinatorialManifoldWithBoundary]
  have hmap : IsPLHomeomorphOn (Prod.map f id) R.space A.space := by
    rw [hRspace, hAspace]
    exact hfT.prodMap (isPLBall_Icc hab).isPolyhedron.isPLHomeomorphOn_id
  rw [boundaryComplex_space_of_isPLHomeomorphOn R A hR.isCombinatorialManifoldWithBoundary hmap,
    hboundary, _root_.Set.image_union, _root_.Set.prodMap_image_prod, _root_.Set.prodMap_image_prod, _root_.Set.image_id, _root_.Set.image_id,
    hfT.image_eq, ← boundaryComplex_space_of_isPLHomeomorphOn T K
      hT.isCombinatorialManifoldWithBoundary hfT]

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prism_one with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prism_one"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prism_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prism_one

theorem IsCombinatorialManifoldWithBoundary.prod_Icc_one
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) {a b : ℝ} (hab : a < b)
    (R : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite R.faces]
    (hRspace : R.space = K.space ×ˢ _root_.Set.Icc a b) : IsCombinatorialManifoldWithBoundary 2 R := by
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods
  intro p hp
  have hp' : p ∈ K.space ×ˢ _root_.Set.Icc a b := hRspace ▸ hp
  obtain ⟨A, hA, hAK, hAnhds⟩ :=
    hK.exists_isPLBall_subset_of_mem_nhdsWithin hp'.1 self_mem_nhdsWithin
  refine ⟨A ×ˢ _root_.Set.Icc a b, isPLBall_two_prod hA (isPLBall_Icc hab), ?_, ?_⟩
  · rw [hRspace]
    exact _root_.Set.prod_mono (hAK.trans _root_.Set.inter_subset_left) Subset.rfl
  · rw [hRspace]
    exact nhdsWithin_prod hAnhds self_mem_nhdsWithin

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.prod_Icc_one with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.prod_Icc_one"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.prod_Icc_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.prod_Icc_one

open _root_.Classical in
theorem boundaryComplex_space_prod_Icc_one [d : DecidableEq (E × ℝ)]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 1 K) {a b : ℝ} (hab : a < b)
    (R : Geometry.SimplicialComplex ℝ (E × ℝ)) [Finite R.faces]
    (hRspace : R.space = K.space ×ˢ _root_.Set.Icc a b) :
    (boundaryComplex 2 R).space =
      K.space ×ˢ {a, b} ∪ (boundaryComplex 1 K).space ×ˢ _root_.Set.Icc a b := by
  have hd : d = fun x y => Classical.propDecidable (x = y) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hR := hK.prod_Icc_one K hab R hRspace
  have hsub : K.space ×ˢ {a, b} ∪ (boundaryComplex 1 K).space ×ˢ _root_.Set.Icc a b ⊆ R.space := by
    rw [hRspace]
    rintro p (⟨hp, ht⟩ | ⟨hp, ht⟩)
    · rcases ht with rfl | rfl
      · exact ⟨hp, le_rfl, hab.le⟩
      · exact ⟨hp, hab.le, le_rfl⟩
    · exact ⟨boundaryComplex_space_subset 1 K hp, ht⟩
  ext p
  by_cases hp : p ∈ R.space
  · have hp' : p ∈ K.space ×ˢ _root_.Set.Icc a b := hRspace ▸ hp
    obtain ⟨D, hD, hDK, hDnhds⟩ :=
      hK.exists_isPLBall_subset_of_mem_nhdsWithin hp'.1 self_mem_nhdsWithin
    obtain ⟨A, hAfin, hAspace⟩ := hD.isPolyhedron.exists_simplicialComplex
    let _ : Finite A.faces := hAfin.to_subtype
    have hA : IsPLBall 1 A.space := hAspace.symm ▸ hD
    have hAK : A.space ⊆ K.space := hAspace.subset.trans (hDK.trans _root_.Set.inter_subset_left)
    have hAnhds : A.space ∈ 𝓝[K.space] p.1 := hAspace.symm ▸ hDnhds
    have hpA : p.1 ∈ A.space := mem_of_mem_nhdsWithin hp'.1 hAnhds
    have hprod := isPLBall_two_prod hA (isPLBall_Icc hab)
    obtain ⟨Q, hQfin, hQspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
    let _ : Finite Q.faces := hQfin.to_subtype
    have hQ : IsPLBall 2 Q.space := hQspace.symm ▸ hprod
    have hQR : Q.space ⊆ R.space := by
      rw [hQspace, hRspace]
      exact _root_.Set.prod_mono hAK Subset.rfl
    have hpQ : p ∈ Q.space := hQspace.symm ▸ ⟨hpA, hp'.2⟩
    have hQnhds : Q.space ∈ 𝓝[R.space] p := by
      rw [hQspace, hRspace]
      exact nhdsWithin_prod hAnhds self_mem_nhdsWithin
    have hloc := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin R Q hR
      hQ.isCombinatorialManifoldWithBoundary hQR hpQ hQnhds
    have hlocA := mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K A hK
      hA.isCombinatorialManifoldWithBoundary hAK hpA hAnhds
    rw [← hloc, boundaryComplex_space_prism_one A hA hab Q hQspace]
    simp only [_root_.Set.mem_union, _root_.Set.mem_prod, hpA, hp'.1, hp'.2, hlocA, true_and, and_true]
  · exact iff_of_false (fun hx => hp (boundaryComplex_space_subset 2 R hx))
      (fun hx => hp (hsub hx))

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prod_Icc_one with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prod_Icc_one"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prod_Icc_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_prod_Icc_one

end DifferentialGeometry.Topology.PiecewiseLinear
