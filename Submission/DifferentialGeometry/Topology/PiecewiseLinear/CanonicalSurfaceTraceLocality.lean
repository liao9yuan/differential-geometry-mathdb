/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceWindow
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceLocality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.boundary_subset_interior_outer
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    T'' i ⊆ interior (φ '' S i) := by
  have hinner : S'' i ⊆ interior (φ '' S i) := by
    simpa using (htw.config i).innerSubset 0
  exact (htw.boundary_subset_solid i).trans hinner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.boundary_subset_interior_outer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.boundary_subset_interior_outer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.boundary_subset_interior_outer ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.boundary_subset_interior_outer

theorem IsCanonicalTower.inter_even_of_sdiff_eq
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {L L' : Set E3} {i k : ℤ} (hki : k ≠ i)
    (heq : L' \ interior (φ '' S (2 * i)) = L \ interior (φ '' S (2 * i))) :
    L' ∩ T'' (2 * k) = L ∩ T'' (2 * k) := by
  have hdis : Disjoint (T'' (2 * k)) (interior (φ '' S (2 * i))) :=
    (htw.apart (2 * k) (2 * i) (by rw [le_abs]; omega)).mono
      (htw.boundary_subset_outer _) interior_subset
  ext x
  exact ⟨fun hx => ⟨(heq.subset ⟨hx.1, disjoint_left.mp hdis hx.2⟩).1, hx.2⟩,
    fun hx => ⟨(heq.symm.subset ⟨hx.1, disjoint_left.mp hdis hx.2⟩).1, hx.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_of_sdiff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_of_sdiff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_of_sdiff_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_of_sdiff_eq

theorem IsCanonicalTower.hasFiniteCollaredTrace_of_sdiff_eq
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {L L' : Set E3} {i k : ℤ} (hki : k ≠ i) (htrace : HasFiniteCollaredTrace L (T'' (2 * k)))
    (hL' : IsPolyhedron L')
    (heq : L' \ interior (φ '' S (2 * i)) = L \ interior (φ '' S (2 * i))) :
    HasFiniteCollaredTrace L' (T'' (2 * k)) := by
  have hdis : Disjoint (interior (φ '' S (2 * k))) (interior (φ '' S (2 * i))) :=
    (htw.apart (2 * k) (2 * i) (by rw [le_abs]; omega)).mono
      interior_subset interior_subset
  apply htrace.of_locally_eq hL' isOpen_interior (htw.boundary_subset_interior_outer _)
  ext x
  exact ⟨fun hx => ⟨(heq.subset ⟨hx.1, disjoint_left.mp hdis hx.2⟩).1, hx.2⟩,
    fun hx => ⟨(heq.symm.subset ⟨hx.1, disjoint_left.mp hdis hx.2⟩).1, hx.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.hasFiniteCollaredTrace_of_sdiff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.hasFiniteCollaredTrace_of_sdiff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.hasFiniteCollaredTrace_of_sdiff_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.hasFiniteCollaredTrace_of_sdiff_eq

theorem IsCanonicalTower.inter_even_eq_sdiff_of_local_replacement
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {L L' G : Set E3} {i : ℤ} (hG : G ⊆ T'' (2 * i))
    (hout : L' \ interior (φ '' S (2 * i)) = L \ interior (φ '' S (2 * i)))
    (hcur : L' ∩ T'' (2 * i) = (L ∩ T'' (2 * i)) \ G) (k : ℤ) :
    L' ∩ T'' (2 * k) = (L ∩ T'' (2 * k)) \ G := by
  by_cases hki : k = i
  · exact hki ▸ hcur
  · rw [htw.inter_even_of_sdiff_eq hki hout]
    have hdis : Disjoint (T'' (2 * k)) G :=
      (htw.apart (2 * k) (2 * i) (by rw [le_abs]; omega)).mono
        (htw.boundary_subset_outer _) (hG.trans (htw.boundary_subset_outer _))
    exact Set.ext fun x => ⟨fun hx => ⟨hx, disjoint_left.mp hdis hx.2⟩, fun hx => hx.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_eq_sdiff_of_local_replacement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_eq_sdiff_of_local_replacement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_eq_sdiff_of_local_replacement ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCanonicalTower.inter_even_eq_sdiff_of_local_replacement

end DifferentialGeometry.Topology.PiecewiseLinear
