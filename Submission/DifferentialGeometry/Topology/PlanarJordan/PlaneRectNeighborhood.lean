/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PlanarJordan.PlanarArcSmoothing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology.PlanarJordan

open _root_.Submission.Schoenflies (Plane)

theorem ball_subset_planeRect {x : Plane} {r a b c d : ℝ}
    (ha : a ≤ x 0 - r) (hb : x 0 + r ≤ b)
    (hc : c ≤ x 1 - r) (hd : x 1 + r ≤ d) :
    ball x r ⊆ planeRect a b c d := by
  intro y hy
  have h0 := (planeAbsSub_le_dist y x 0).trans_lt (mem_ball.mp hy)
  have h1 := (planeAbsSub_le_dist y x 1).trans_lt (mem_ball.mp hy)
  rw [abs_lt] at h0 h1
  exact ⟨by linarith [h0.1], by linarith [h0.2],
    by linarith [h1.1], by linarith [h1.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PlanarJordan.ball_subset_planeRect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PlanarJordan.ball_subset_planeRect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PlanarJordan.ball_subset_planeRect ``Submission.DifferentialGeometry.Topology.PlanarJordan.ball_subset_planeRect

end DifferentialGeometry.Topology.PlanarJordan
