/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FreeCellSlab
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FiberBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FaceInterior
import Submission.DifferentialGeometry.Topology.SlabBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell
    (K A : Geometry.SimplicialComplex ℝ E) [Finite A.faces]
    (hAK : A.faces ⊆ K.faces) (hdim : Module.finrank ℝ E = 3)
    {T : Finset E} (hT : T ∈ A.faces) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : _root_.Set.InjOn ℓ K.vertices) {a b r : ℝ} (hab : a < b) (hr : r ∈ _root_.Set.Icc a b)
    (hvertices : ∀ v ∈ T, ℓ v < a ∨ b < ℓ v)
    {L : Geometry.SimplicialComplex ℝ E} {cells : Finset (Set E)}
    (hL : IsPLDiskDecomposition L cells) (hLspace : L.space = A.space ∩ {x | ℓ x = r})
    (hC : convexHull ℝ (T : Set E) ∩ {x | ℓ x = r} ∈ cells)
    (hfree : IsFreeDiskCell L (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r})) :
    IsPLBall 2 (frontier (A.space ∩ ℓ ⁻¹' _root_.Set.Icc a b) ∩
      (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b)) := by
  classical
  let _ : Finite L.faces := hL.finite_faces.to_subtype
  let B := restrict K (frontier A.space)
  have hB : B.space = frontier A.space := restrict_space_frontier_of_faces_subset K A hAK
  have htrace : (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ∩ (boundaryComplex 2 L).space =
      (convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}) ∩ B.space := by
    ext x
    by_cases hx : x ∈ convexHull ℝ (T : Set E) ∩ {x | ℓ x = r}
    · have hxnot : x ∉ K.vertices := by
        intro hxv
        have hxT := mem_of_mem_convexHull_of_singleton_mem K hxv (hAK hT) hx.1
        rcases hvertices x hxT with hxa | hbx
        · exact hxa.not_ge (hx.2.symm ▸ hr.1)
        · exact hbx.not_ge (hx.2.symm ▸ hr.2)
      have hiff := mem_frontier_space_iff_mem_boundaryComplex_fiber_of_injOn K A L hAK
        hdim hL.isPLBall ℓ.toLinearMap hinj hLspace (A.convexHull_subset_space hT hx.1) hx.2 hxnot
      simp only [_root_.Set.mem_inter_iff, hx, true_and, hB]
      exact hiff.symm
    · simp only [_root_.Set.mem_inter_iff, hx, false_and]
  have hpatch := isPLBall_slab_patch_of_isFreeDiskCell K B (restrict_faces_subset K _)
    (hAK hT) ℓ.toLinearMap hab hr hvertices hL htrace hC hfree
  rw [Topology.frontier_inter_preimage_Icc_of_ne_zero (isPolyhedron_space A).isClosed ℓ hℓ hab.le]
  convert hpatch using 1
  ext x
  have hmem (hx : x ∈ convexHull ℝ (T : Set E)) : x ∈ A.space ∧ x ∈ K.space :=
    ⟨A.convexHull_subset_space hT hx, K.convexHull_subset_space (hAK hT) hx⟩
  simp only [hB, _root_.Set.mem_inter_iff, _root_.Set.mem_union, _root_.Set.mem_preimage, _root_.Set.mem_Icc, _root_.Set.mem_insert_iff,
    _root_.Set.mem_singleton_iff, _root_.Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hside | hends, hx, habx⟩
    · exact ⟨⟨hx, habx⟩, Or.inl hside⟩
    · exact ⟨⟨hx, habx⟩, Or.inr ⟨(hmem hx).2, hends.2⟩⟩
  · rintro ⟨⟨hx, habx⟩, hside | hends⟩
    · exact ⟨Or.inl hside, hx, habx⟩
    · exact ⟨Or.inr ⟨(hmem hx).1, hends.2⟩, hx, habx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_frontier_slab_inter_cell_of_isFreeDiskCell

end DifferentialGeometry.Topology.PiecewiseLinear
