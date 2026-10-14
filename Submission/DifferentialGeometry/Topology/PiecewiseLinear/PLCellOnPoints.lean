/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceRestriction
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.boundary_eq_empty
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {S B : Set M} (h : IsPLCellOn 0 S B) : B = ∅ := by
  obtain ⟨P, r, u, -, -, -, hB⟩ := h
  simpa only [stdSimplexBoundary_zero, _root_.Set.image_empty] using hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.boundary_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.boundary_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.boundary_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.boundary_eq_empty

theorem LocallyFinitePLPieceIn.isPLCellOn_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {U : Set M} (T : LocallyFinitePLPieceIn E 3 M U) {x : E} (hx : x ∈ T.complex.space) :
    IsPLCellOn 0 {T.map x} ∅ := by
  have hball : IsPLBall 0 ({x} : Set E) :=
    ⟨fun _ => x, isPLHomeomorphOn_const_stdSimplex_fin_one x⟩
  obtain ⟨B, hB⟩ := T.exists_isPLCellOn_image (singleton_subset_iff.mpr hx) (by omega) hball
  rw [_root_.Set.image_singleton] at hB
  exact hB.boundary_eq_empty ▸ hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_singleton ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.isPLCellOn_singleton

end DifferentialGeometry.Topology.PiecewiseLinear
