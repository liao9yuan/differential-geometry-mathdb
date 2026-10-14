/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PlanarChainUnion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSpineRevolutionOfOfMemCellInterior
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterTorusTransport
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem revolutionOf_iUnion {ι : Type*} (D : ι → Set E3) :
    revolutionOf (⋃ i, D i) = ⋃ i, revolutionOf (D i) := by
  ext x
  constructor
  · rintro ⟨q, hq, hrest⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact mem_iUnion.mpr ⟨i, q, hi, hrest⟩
  · intro hx
    obtain ⟨i, q, hq, hrest⟩ := mem_iUnion.mp hx
    exact ⟨q, mem_iUnion.mpr ⟨i, hq⟩, hrest⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.revolutionOf_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.revolutionOf_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.revolutionOf_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.revolutionOf_iUnion

section Triple

variable {P : Fin 4 → E3} {D Dint : Fin 3 → Set E3} {J : Fin 4 → Set E3}
  {A S T : Fin 3 → Set E3}

theorem IsRevolvedTorusChain.isSpine_iUnion (hc : IsRevolvedTorusChain P D Dint J A S T) :
    IsSpine (⋃ j, S j) (J 0) := by
  obtain ⟨U, hU, hDU⟩ := hc.chain.exists_cell_iUnion
  have hp : P 0 ∈ Dint 0 := by
    simpa using hc.chain.segmentSubset 0 (left_mem_segment ℝ (P 0) (P 1))
  have hhalf : ∀ q ∈ ⋃ j, D j, q 2 = 0 ∧ 0 < q 0 := by
    intro q hq
    obtain ⟨j, hj⟩ := mem_iUnion.mp hq
    exact hc.chain.halfPlane j q hj
  have hsp := isSpine_revolutionOf_of_mem_cellInterior hU hhalf (hDU 0 hp)
  have hsolid : revolutionOf (⋃ j, D j) = ⋃ j, S j := by
    rw [revolutionOf_iUnion]
    exact _root_.Set.iUnion_congr fun j => (hc.solidEq j).symm
  rw [hsolid, ← hc.circleEq 0] at hsp
  exact hsp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsRevolvedTorusChain.isSpine_iUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsRevolvedTorusChain.isSpine_iUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsRevolvedTorusChain.isSpine_iUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsRevolvedTorusChain.isSpine_iUnion

theorem IsCanonicalConfiguration.isSpine_image_union {N : Set E3} {φ : E3 → E3}
    {S'' T'' : Fin 3 → Set E3}
    (hc : IsCanonicalConfiguration P D Dint J A S T N φ S'' T'') :
    IsSpine (φ '' N) (φ '' J 0) := by
  have hsp : IsSpine N (J 0) := hc.unionEq.symm ▸ hc.base.isSpine_iUnion
  exact hsp.image_of_isEmbedding hc.isEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalConfiguration.isSpine_image_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalConfiguration.isSpine_image_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalConfiguration.isSpine_image_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalConfiguration.isSpine_image_union

end Triple

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.outer_triple_isTopologicalSolidTorus
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    IsTopologicalSolidTorus ((φ '' S i ∪ φ '' S (i + 1)) ∪ φ '' S (i + 2)) := by
  have hsolid := (htw.config i).isSpine_image_union.isTopologicalSolidTorus
  have heq : φ '' (⋃ j : Fin 3, S (i + ((j : ℕ) : ℤ))) =
      (φ '' S i ∪ φ '' S (i + 1)) ∪ φ '' S (i + 2) := by
    rw [_root_.Set.image_iUnion]
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      fin_cases j
      · exact Or.inl (Or.inl (by simpa using hj))
      · exact Or.inl (Or.inr (by simpa using hj))
      · exact Or.inr (by simpa using hj)
    · rintro ((hx | hx) | hx)
      · exact mem_iUnion.mpr ⟨0, by simpa using hx⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using hx⟩
      · exact mem_iUnion.mpr ⟨2, by simpa using hx⟩
  exact heq ▸ hsolid

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.outer_triple_isTopologicalSolidTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.outer_triple_isTopologicalSolidTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.outer_triple_isTopologicalSolidTorus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.outer_triple_isTopologicalSolidTorus

end DifferentialGeometry.Topology.PiecewiseLinear
