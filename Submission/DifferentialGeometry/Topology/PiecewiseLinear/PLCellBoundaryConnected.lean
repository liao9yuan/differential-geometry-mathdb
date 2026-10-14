/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isConnected_boundary {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {n : ℕ} {S B : Set M}
    (h : IsPLCellOn (n + 2) S B) : IsConnected B := by
  obtain ⟨P, r, u, hr, hu, -, rfl⟩ := h
  have hsub : r '' stdSimplexBoundary (n + 2) ⊆ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hr.bijOn.mapsTo hz.1
  exact (hr.isPLSphere_image_stdSimplexBoundary (n := n + 1)).isConnected.image u
    (hu.continuousOn.mono hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isConnected_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
