/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem IsPLCellOn.closure_sdiff_boundary {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) :
    closure (S \ B) = S := by
  have hSc := hS.isCompact.isClosed
  cases d with
  | zero =>
    have hB : B = ∅ := by
      obtain ⟨P, r, u, -, -, -, hB⟩ := hS
      rw [hB, stdSimplexBoundary_zero, _root_.Set.image_empty, _root_.Set.image_empty]
    rw [hB, _root_.Set.sdiff_empty, hSc.closure_eq]
  | succ n =>
    refine Subset.antisymm (closure_minimal _root_.Set.sdiff_subset hSc) ?_
    obtain ⟨P, r, u, hr, hu, hSE, hBE⟩ := hS
    have hBd : r '' stdSimplexBoundary (n + 1) ⊆ P := by
      rintro _ ⟨x, hx, rfl⟩
      exact hr.bijOn.mapsTo hx.1
    rw [hSE, hBE, ← hu.injOn.image_sdiff_subset hBd]
    have hcl := hr.closure_sdiff_image_stdSimplexBoundary (n := n)
    calc u '' P = u '' closure (P \ r '' stdSimplexBoundary (n + 1)) := by rw [hcl]
      _ ⊆ closure (u '' (P \ r '' stdSimplexBoundary (n + 1))) :=
        ContinuousOn.image_closure (by rw [hcl]; exact hu.continuousOn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.closure_sdiff_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.closure_sdiff_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.closure_sdiff_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.closure_sdiff_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
