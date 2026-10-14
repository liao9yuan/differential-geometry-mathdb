/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConsecutiveCellUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isTopologicalCell_planar_union {A B : Set E3}
    (hA : IsTopologicalCell 2 A) (hB : IsTopologicalCell 2 B)
    (hAB : IsTopologicalCell 2 (A ∩ B))
    (hAp : ∀ p ∈ A, p 2 = 0) (hBp : ∀ p ∈ B, p 2 = 0) :
    IsTopologicalCell 2 (A ∪ B) := by
  have hInt : IsTopologicalCell 2 (planarProjection '' A ∩ planarProjection '' B) := by
    rw [← planarProjection_image_inter hAp hBp]
    exact isTopologicalCell_of_planarProjection (fun p hp => hAp p hp.1) hAB
  have hproj := PlanarJordan.isTopologicalCell_union_of_isTopologicalCell_inter
    (isTopologicalCell_of_planarProjection hAp hA)
    (isTopologicalCell_of_planarProjection hBp hB) hInt
  have himage : planarPoint '' (planarProjection '' A ∪ planarProjection '' B) = A ∪ B := by
    rw [_root_.Set.image_union, planarPoint_image_planarProjection_image hAp,
      planarPoint_image_planarProjection_image hBp]
  exact himage ▸ isTopologicalCell_planarPoint_image hproj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalCell_planar_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalCell_planar_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalCell_planar_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isTopologicalCell_planar_union

variable {P : Fin 4 → E3} {D Dint : Fin 3 → Set E3}

theorem IsPlanarCellChain.isTopologicalCell_iUnion (hc : IsPlanarCellChain P D Dint) :
    IsTopologicalCell 2 (⋃ j, D j) := by
  have hplanar (j : Fin 3) : ∀ p ∈ D j, p 2 = 0 := fun p hp => (hc.halfPlane j p hp).1
  have h01 : IsTopologicalCell 2 (D 0 ∪ D 1) :=
    isTopologicalCell_planar_union (hc.cell 0).isTopologicalCell (hc.cell 1).isTopologicalCell
      (by simpa using hc.overlap 0) (hplanar 0) (hplanar 1)
  have hInt : IsTopologicalCell 2 ((D 0 ∪ D 1) ∩ D 2) := by
    rw [_root_.Set.union_inter_distrib_right, hc.apart, _root_.Set.empty_union]
    simpa using hc.overlap 1
  have h012 : IsTopologicalCell 2 ((D 0 ∪ D 1) ∪ D 2) :=
    isTopologicalCell_planar_union h01 (hc.cell 2).isTopologicalCell hInt
      (fun p hp => hp.elim (hplanar 0 p) (hplanar 1 p)) (hplanar 2)
  have hUnion : (⋃ j, D j) = (D 0 ∪ D 1) ∪ D 2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      fin_cases j
      · exact Or.inl (Or.inl hj)
      · exact Or.inl (Or.inr hj)
      · exact Or.inr hj
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
      · exact mem_iUnion.mpr ⟨2, hx⟩
  exact hUnion.symm ▸ h012

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.isTopologicalCell_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.isTopologicalCell_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.isTopologicalCell_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.isTopologicalCell_iUnion

theorem IsPlanarCellChain.exists_cell_iUnion (hc : IsPlanarCellChain P D Dint) :
    ∃ U : Set E3, IsTopologicalCellWithInterior 2 (⋃ j, D j) U ∧ ∀ j, Dint j ⊆ U := by
  obtain ⟨e⟩ := hc.isTopologicalCell_iUnion
  let U : Set E3 := Subtype.val ''
    (e.symm '' {q | ‖(q : EuclideanSpace ℝ (Fin 2))‖ < 1})
  have hU : IsTopologicalCellWithInterior 2 (⋃ j, D j) U := ⟨e.symm, rfl⟩
  exact ⟨U, hU, fun j => (hc.cell j).interior_mono hU (_root_.Set.subset_iUnion D j)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.exists_cell_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.exists_cell_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.exists_cell_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPlanarCellChain.exists_cell_iUnion

end DifferentialGeometry.Topology.PiecewiseLinear
