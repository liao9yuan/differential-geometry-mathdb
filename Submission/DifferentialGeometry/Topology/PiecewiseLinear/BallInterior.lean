/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPLHomeomorphOn.image_openSimplex_stdVertices {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    f '' openSimplex (stdVertices n) = P \ f '' stdSimplexBoundary (n + 1) := by
  rw [openSimplex_eq_sdiff_simplexBoundary (stdVertices n) (stdVertices_affineIndependent n),
    convexHull_stdVertices, simplexBoundary_stdVertices_space,
    hf.bijOn.injOn.image_sdiff_subset (fun _ hx => hx.1), hf.image_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_openSimplex_stdVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_openSimplex_stdVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_openSimplex_stdVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.image_openSimplex_stdVertices

theorem IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    closure (P \ f '' stdSimplexBoundary (n + 1)) = P := by
  rw [← hf.image_openSimplex_stdVertices,
    ← hf.image_closure (isCompact_stdSimplex ℝ _) openSimplex_stdVertices_subset_stdSimplex]
  have hclosure : closure (openSimplex (stdVertices n)) = stdSimplex ℝ (Fin (n + 2)) := by
    apply Subset.antisymm
      (closure_minimal openSimplex_stdVertices_subset_stdSimplex (isClosed_stdSimplex ℝ _))
    intro x hx
    exact convexHull_subset_closure_openSimplex
      (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (two_le_card_stdVertices n)))
      (by rwa [convexHull_stdVertices])
  rw [hclosure, hf.image_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.closure_sdiff_image_stdSimplexBoundary

theorem IsPLHomeomorphOn.isConnected_sdiff_image_stdSimplexBoundary {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    IsConnected (P \ f '' stdSimplexBoundary (n + 1)) := by
  rw [← hf.image_openSimplex_stdVertices]
  exact ((convex_openSimplex (stdVertices n)).isConnected
    ⟨stdCenter n, stdCenter_mem_openSimplex n⟩).image f
      (hf.isPiecewiseAffineOn.continuousOn.mono openSimplex_stdVertices_subset_stdSimplex)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_image_stdSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_image_stdSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_image_stdSimplexBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isConnected_sdiff_image_stdSimplexBoundary

end DifferentialGeometry.Topology.PiecewiseLinear
