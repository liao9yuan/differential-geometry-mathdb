/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplyEmbedded
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
structure IsPLDiskDecomposition (K : Geometry.SimplicialComplex ℝ E)
    (cells : Finset (Set E)) : Prop where
  finite_faces : K.faces.Finite
  isPLBall : IsPLBall 2 K.space
  cell_isPLBall : ∀ C ∈ cells, IsPLBall 2 C
  cell_space : ∀ C ∈ cells, (restrict K C).space = C
  space_eq : K.space = ⋃ C ∈ cells, C
  inter_subset_boundary : ∀ C ∈ cells, ∀ D ∈ cells, C ≠ D →
    C ∩ D ⊆ (boundaryComplex 2 (restrict K C)).space
  inter_isPLBall : ∀ C ∈ cells, ∀ D ∈ cells, C ≠ D → (C ∩ D).Nonempty →
    IsPLBall 0 (C ∩ D) ∨ IsPLBall 1 (C ∩ D)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition

open _root_.Classical in
def IsFreeDiskCell (K : Geometry.SimplicialComplex ℝ E) (C : Set E) : Prop :=
  IsPLBall 1 ((boundaryComplex 2 (restrict K C)).space ∩ (boundaryComplex 2 K).space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDiskCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDiskCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDiskCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsFreeDiskCell

theorem IsPLDiskDecomposition.cell_subset {K : Geometry.SimplicialComplex ℝ E}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells) {C : Set E}
    (hC : C ∈ cells) : C ⊆ K.space := by
  rw [h.space_eq]
  exact _root_.Set.subset_iUnion_of_subset C (_root_.Set.subset_iUnion_of_subset hC Subset.rfl)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cell_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cell_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cell_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cell_subset

theorem IsPLDiskDecomposition.cells_nonempty {K : Geometry.SimplicialComplex ℝ E}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells) : cells.Nonempty := by
  obtain ⟨x, hx⟩ := h.isPLBall.nonempty
  rw [h.space_eq] at hx
  obtain ⟨C, hC, _⟩ := mem_iUnion₂.mp hx
  exact ⟨C, hC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cells_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cells_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cells_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.cells_nonempty

open _root_.Classical in
theorem IsPLDiskDecomposition.inter_subset_boundaries {K : Geometry.SimplicialComplex ℝ E}
    {cells : Finset (Set E)} (h : IsPLDiskDecomposition K cells) {C D : Set E}
    (hC : C ∈ cells) (hD : D ∈ cells) (hne : C ≠ D) :
    C ∩ D ⊆ (boundaryComplex 2 (restrict K C)).space ∩
      (boundaryComplex 2 (restrict K D)).space := by
  refine _root_.Set.subset_inter (h.inter_subset_boundary C hC D hD hne) ?_
  rw [_root_.Set.inter_comm]
  exact h.inter_subset_boundary D hD C hC hne.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.inter_subset_boundaries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.inter_subset_boundaries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.inter_subset_boundaries ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLDiskDecomposition.inter_subset_boundaries

open _root_.Classical in
structure SchoenfliesInput : Prop where
  isSimplyEmbedded_frontier_of_convex :
    ∀ C : Set (EuclideanSpace ℝ (Fin 3)), Convex ℝ C → IsPLBall 3 C →
      IsSimplyEmbedded (frontier C)
  isSimplyEmbedded_frontier_coneComplex :
    ∀ (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (p : EuclideanSpace ℝ (Fin 3)) (hL : IsConeBase p L),
      L.faces.Finite → IsPLBall 2 L.space → IsSimplyEmbedded (frontier (coneComplex hL).space)
  isSimplyEmbedded_union_sdiff_diskInterior :
    ∀ (S₁ S₂ D : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (r : ℝ),
      IsSimplyEmbedded S₁ → IsSimplyEmbedded S₂ →
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D →
      ℓ ≠ 0 → D ⊆ {x | ℓ x = r} → S₁ ∩ S₂ = D →
      IsSimplyEmbedded ((S₁ ∪ S₂) \ (D \ (f '' stdSimplexBoundary 2)))
  exists_two_free_disk_cells :
    ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (cells : Finset (Set (EuclideanSpace ℝ (Fin 3)))),
      IsPLDiskDecomposition K cells → 1 < cells.card →
      ∃ C ∈ cells, ∃ D ∈ cells, C ≠ D ∧ IsFreeDiskCell K C ∧ IsFreeDiskCell K D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput

theorem SchoenfliesInput.exists_free_disk_cell_ne (I : SchoenfliesInput)
    {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
    {cells : Finset (Set (EuclideanSpace ℝ (Fin 3)))}
    (h : IsPLDiskDecomposition K cells) (hmore : 1 < cells.card)
    (C₀ : Set (EuclideanSpace ℝ (Fin 3))) :
    ∃ C ∈ cells, C ≠ C₀ ∧ IsFreeDiskCell K C := by
  obtain ⟨C, hC, D, hD, hne, hfreeC, hfreeD⟩ := I.exists_two_free_disk_cells K cells h hmore
  by_cases hCC₀ : C = C₀
  · exact ⟨D, hD, hCC₀ ▸ hne.symm, hfreeD⟩
  · exact ⟨C, hC, hCC₀, hfreeC⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput.exists_free_disk_cell_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput.exists_free_disk_cell_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput.exists_free_disk_cell_ne ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesInput.exists_free_disk_cell_ne

end DifferentialGeometry.Topology.PiecewiseLinear
