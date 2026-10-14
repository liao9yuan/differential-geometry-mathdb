/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollarNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_eqOn_boundary_disk
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hB : IsPLSphere 2 (boundaryComplex 3 K).space)
    {P W : Set E} (hP : IsPLBall 2 P) {a b : ℝ} (hab : a < b)
    {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (P ×ˢ _root_.Set.Icc a b) W)
    (hWK : W ⊆ K.space) (hbottom : ∀ x ∈ P, ρ (x, a) = x)
    (hWB : W ∩ (boundaryComplex 3 K).space = P) :
    ∃ (W' : Set E) (σ : E × ℝ → E),
      IsPolyhedron W' ∧ W' ⊆ K.space ∧
      W' ∈ 𝓝ˢ[K.space] (boundaryComplex 3 K).space ∧
      IsPLHomeomorphOn σ ((boundaryComplex 3 K).space ×ˢ _root_.Set.Icc a b) W' ∧
      _root_.Set.EqOn σ ρ (P ×ˢ _root_.Set.Icc a b) ∧
      (∀ x ∈ (boundaryComplex 3 K).space, σ (x, a) = x) ∧
      W' ∩ (boundaryComplex 3 K).space = (boundaryComplex 3 K).space ∧
      _root_.Set.MapsTo σ ((boundaryComplex 3 K).space ×ˢ _root_.Set.Ioc a b)
        (K.space \ (boundaryComplex 3 K).space) := by
  classical
  let B := (boundaryComplex 3 K).space
  have hPB : P ⊆ B := hWB.symm.subset.trans _root_.Set.inter_subset_right
  have hW : IsPLBall 3 W :=
    (isPLBall_three_prod hP (isPLBall_Icc hab)).of_isPLHomeomorphOn hρ
  obtain ⟨D, hDfin, hDspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite D.faces := hDfin.to_subtype
  have hD : IsPLBall 2 D.space := hDspace.symm ▸ hP
  let Q := closure (B \ P)
  have hQ : IsPLBall 2 Q := hB.isPLBall_closure_sdiff hP hPB
  have hQB : Q ⊆ B := closure_minimal _root_.Set.sdiff_subset hB.isPolyhedron.isClosed
  obtain ⟨J, hJfin, hJspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite J.faces := hJfin.to_subtype
  have hJ : IsPLBall 2 J.space := hJspace.symm ▸ hQ
  have hJB : J.space ⊆ B := hJspace.subset.trans hQB
  have hmeet : J.space ∩ P = (boundaryComplex 2 J).space := by
    obtain ⟨q, hq⟩ := hQ
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex J (hJspace.symm ▸ hq),
      simplexBoundary_stdVertices_space, hJspace]
    exact (hB.image_stdSimplexBoundary_complement hP hPB hq).symm
  have hsideD : J.space ∩ P ⊆ (boundaryComplex 2 D).space := by
    obtain ⟨p, hp⟩ := hP
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D (hDspace.symm ▸ hp),
      simplexBoundary_stdVertices_space, hJspace, _root_.Set.inter_comm]
    exact (hB.inter_closure_sdiff_eq_image_stdSimplexBoundary hp hPB).subset
  have hcover : P ∪ J.space = B := by
    apply Subset.antisymm (_root_.Set.union_subset hPB hJB)
    intro x hx
    by_cases hxP : x ∈ P
    · exact Or.inl hxP
    · exact Or.inr (hJspace.symm.subset (subset_closure ⟨hx, hxP⟩))
  obtain ⟨L, hLfin, hLspace⟩ := hW.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 3 L.space := hLspace.symm ▸ hW
  have hLK : L.space ⊆ K.space := hLspace.subset.trans hWK
  have hρL : IsPLHomeomorphOn ρ (D.space ×ˢ _root_.Set.Icc a b) L.space := by
    rw [hDspace, hLspace]
    exact hρ
  obtain ⟨R, hRfin, hR, hRspace⟩ :=
    hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff hW hWK (hWB.symm ▸ hP)
  let _ : Finite R.faces := hRfin.to_subtype
  have hRspaceL : R.space = closure (K.space \ L.space) := by rwa [hLspace]
  have hRK : R.space ⊆ K.space := by
    rw [hRspace]
    exact closure_minimal _root_.Set.sdiff_subset (isPolyhedron_space K).isClosed
  have hWR : W ∩ R.space ⊆ (boundaryComplex 3 R).space := by
    rw [← hLspace]
    exact inter_space_complement_subset_boundaryComplex K L R hK
      hL.isCombinatorialManifoldWithBoundary hLK hR hRspaceL
  have hBR : B ∩ R.space ⊆ (boundaryComplex 3 R).space := by
    rw [_root_.Set.inter_comm]
    exact inter_boundaryComplex_space_subset_of_subset K R hK hR hRK
  have hboundaryR := boundaryComplex_space_of_closure_sdiff K L R hK
    hL.isCombinatorialManifoldWithBoundary hLK hR hRspaceL
  have hbase : J.space ⊆ (boundaryComplex 3 R).space := by
    rw [hboundaryR]
    apply Subset.trans _ _root_.Set.subset_union_left
    rw [hJspace]
    apply closure_mono
    rintro x ⟨hxB, hxP⟩
    exact ⟨hxB, fun hxL => hxP (hWB.subset ⟨hLspace.subset hxL, hxB⟩)⟩
  have hside : ρ '' ((J.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 L).space :=
    image_prism_side_subset_boundaryComplex D L hD hab hρL hsideD
  have hpositive : ρ '' ((J.space ∩ P) ×ˢ _root_.Set.Ioc a b) ⊆
      (boundaryComplex 3 L).space \ B := by
    rintro x ⟨z, hz, rfl⟩
    refine ⟨hside ⟨z, ⟨hz.1, _root_.Set.Ioc_subset_Icc_self hz.2⟩, rfl⟩, ?_⟩
    intro hzB
    have hzρ := hρ.bijOn.mapsTo ⟨hz.1.2, _root_.Set.Ioc_subset_Icc_self hz.2⟩
    have hzP := hWB.subset ⟨hzρ, hzB⟩
    have heq := hρ.bijOn.injOn ⟨hz.1.2, _root_.Set.Ioc_subset_Icc_self hz.2⟩
      ⟨hzP, le_rfl, hab.le⟩ (hbottom (ρ z) hzP).symm
    exact hz.2.1.ne' (congrArg Prod.snd heq)
  have hclosure : closure (ρ '' ((J.space ∩ P) ×ˢ _root_.Set.Ioc a b)) =
      ρ '' ((J.space ∩ P) ×ˢ _root_.Set.Icc a b) := by
    rw [← hρ.image_closure (hP.isPolyhedron.isCompact.prod _root_.CompactIccSpace.isCompact_Icc)
      (_root_.Set.prod_mono _root_.Set.inter_subset_right _root_.Set.Ioc_subset_Icc_self), closure_prod_eq,
      ((isPolyhedron_space J).isClosed.inter hP.isPolyhedron.isClosed).closure_eq,
      closure_Ioc hab.ne]
  have hsideR : ρ '' ((J.space ∩ P) ×ˢ _root_.Set.Icc a b) ⊆ (boundaryComplex 3 R).space := by
    rw [hboundaryR, ← hclosure]
    exact (closure_mono hpositive).trans _root_.Set.subset_union_right
  obtain ⟨C, σ, -, hC, hCR, -, hσ, hσρ, hσbottom, hσB, hσpositive, -⟩ :=
    exists_collar_extension_of_boundary J R hJ hR hP.isPolyhedron hJB hab hρ
      hbottom hWB hmeet (_root_.Set.union_subset hbase hsideR) hWR hBR (U := _root_.Set.univ) Filter.univ_mem
  rw [hcover] at hσ hσbottom hσB hσpositive
  have hsub : W ∪ C ⊆ K.space := _root_.Set.union_subset hWK (hCR.trans hRK)
  refine ⟨W ∪ C, σ, hW.isPolyhedron.union hC.isPolyhedron, hsub,
    hσ.mem_nhdsSetWithin_boundaryComplex K hK hab hsub hσbottom,
    hσ, hσρ, hσbottom, hσB, ?_⟩
  exact hσpositive.mono_right (_root_.Set.sdiff_subset_sdiff_left hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_collar_eqOn_boundary_disk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_collar_eqOn_boundary_disk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_collar_eqOn_boundary_disk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.exists_collar_eqOn_boundary_disk

end DifferentialGeometry.Topology.PiecewiseLinear
