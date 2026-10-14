/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexSection
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem interior_convexHull_inter_slab_nonempty
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = Module.finrank ℝ E + 1) (ℓ : E →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (havoid : ∀ v ∈ T, ℓ v ≠ a ∧ ℓ v ≠ b)
    (hne : (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b).Nonempty) :
    (interior (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b)).Nonempty := by
  obtain ⟨p, hp, hpa, hpb⟩ := hne
  have hinter : (interior (convexHull ℝ (T : Set E))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex hT hcard]
    exact ⟨T.centroid ℝ id, centroid_mem_openSimplex (Finset.card_pos.mp (by omega))⟩
  have hbelow : ∃ x ∈ convexHull ℝ (T : Set E), ℓ x < b := by
    rcases lt_or_eq_of_le hpb with hpb | hpb
    · exact ⟨p, hp, hpb⟩
    · obtain ⟨⟨v, hv, hvb⟩, -⟩ := exists_lt_and_gt_of_mem_convexHull_fiber T ℓ
        (fun v hv => (havoid v hv).2) ⟨p, hp, hpb⟩
      exact ⟨v, subset_convexHull ℝ _ hv, hvb⟩
  have habove : ∃ x ∈ convexHull ℝ (T : Set E), a < ℓ x := by
    rcases lt_or_eq_of_le hpa with hpa | hpa
    · exact ⟨p, hp, hpa⟩
    · obtain ⟨-, v, hv, hav⟩ := exists_lt_and_gt_of_mem_convexHull_fiber T ℓ
        (fun v hv => (havoid v hv).1) ⟨p, hp, hpa.symm⟩
      exact ⟨v, subset_convexHull ℝ _ hv, hav⟩
  obtain ⟨x, hx, hxab⟩ := Topology.exists_mem_interior_preimage_Ioo_of_convex
    (convex_convexHull ℝ (T : Set E)) hinter ℓ.continuous_of_finiteDimensional hab hbelow habove
  refine ⟨x, ?_⟩
  rw [interior_inter]
  exact ⟨hx, interior_maximal (_root_.Set.preimage_mono _root_.Set.Ioo_subset_Icc_self)
    (isOpen_Ioo.preimage ℓ.continuous_of_finiteDimensional) hxab⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.interior_convexHull_inter_slab_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.interior_convexHull_inter_slab_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.interior_convexHull_inter_slab_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.interior_convexHull_inter_slab_nonempty

theorem closure_interior_convexHull_inter_slab
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : T.card = Module.finrank ℝ E + 1) (ℓ : E →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (havoid : ∀ v ∈ T, ℓ v ≠ a ∧ ℓ v ≠ b) :
    closure (interior (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b)) =
      convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b := by
  by_cases hne : (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b).Nonempty
  · have hpoly : IsHPolytope (convexHull ℝ (T : Set E) ∩ ℓ ⁻¹' _root_.Set.Icc a b) :=
      (isHPolytope_convexHull_of_affineIndependent T hT).inter_preimage isHPolytope_Icc ℓ
    exact (hpoly.convex.closure_interior_eq_closure_of_nonempty_interior
      (interior_convexHull_inter_slab_nonempty T hT hcard ℓ hab havoid hne)).trans
          hpoly.isClosed.closure_eq
  · rw [not_nonempty_iff_eq_empty.mp hne, interior_empty, closure_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_convexHull_inter_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_convexHull_inter_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_convexHull_inter_slab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_convexHull_inter_slab

theorem closure_interior_space_inter_slab
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hreg : closure (interior K.space) = K.space) (ℓ : E →ᵃ[ℝ] ℝ) {a b : ℝ} (hab : a < b)
    (havoid : ∀ v ∈ K.vertices, ℓ v ≠ a ∧ ℓ v ≠ b) :
    closure (interior (K.space ∩ ℓ ⁻¹' _root_.Set.Icc a b)) = K.space ∩ ℓ ⁻¹' _root_.Set.Icc a b := by
  have hclosed : IsClosed (K.space ∩ ℓ ⁻¹' _root_.Set.Icc a b) :=
    (isPolyhedron_space K).isClosed.inter (isClosed_Icc.preimage ℓ.continuous_of_finiteDimensional)
  apply Subset.antisymm (closure_minimal interior_subset hclosed)
  rintro x ⟨hxK, hxab⟩
  obtain ⟨T, hT, hcard, hxT⟩ := exists_face_card_eq_finrank_succ_of_mem_closure K
    isOpen_interior interior_subset (hreg.symm.subset hxK)
  have hTreg := closure_interior_convexHull_inter_slab T (K.indep hT) hcard ℓ hab
    (fun v hv => havoid v (K.down_closed hT (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)))
  exact closure_mono (interior_mono (_root_.Set.inter_subset_inter_left _ (K.convexHull_subset_space hT)))
    (hTreg.symm.subset ⟨hxT, hxab⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_space_inter_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_space_inter_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_space_inter_slab ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_interior_space_inter_slab

end DifferentialGeometry.Topology.PiecewiseLinear
