/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLCellOn.sdiff_boundary_nonempty {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] {d : ℕ} {S B : Set M} (hcell : IsPLCellOn d S B) :
    (S \ B).Nonempty := by
  obtain ⟨P, r, u, hr, hu, rfl, rfl⟩ := hcell
  cases d with
  | zero =>
      rw [stdSimplexBoundary_zero, _root_.Set.image_empty, _root_.Set.image_empty, _root_.Set.sdiff_empty]
      exact (show IsPLBall 0 P from ⟨r, hr⟩).nonempty.image u
  | succ d =>
      have hbd : r '' stdSimplexBoundary (d + 1) ⊆ P := by
        rintro _ ⟨x, hx, rfl⟩
        exact hr.bijOn.mapsTo hx.1
      rw [← hu.injOn.image_sdiff_subset hbd]
      exact hr.isConnected_sdiff_image_stdSimplexBoundary.nonempty.image u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.sdiff_boundary_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.sdiff_boundary_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.sdiff_boundary_nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.sdiff_boundary_nonempty

end DifferentialGeometry.Topology.PiecewiseLinear
