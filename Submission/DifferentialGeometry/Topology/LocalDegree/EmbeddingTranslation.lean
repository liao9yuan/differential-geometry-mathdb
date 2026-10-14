/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.EmbeddingParity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

theorem embeddingOrientationParity_sub_const
    {U : Set E} (hU : IsOpen U) {f : E → E} (hf : ContinuousOn f U)
    (hfi : _root_.Set.InjOn f U) (b : E) (x : U) :
    embeddingOrientationParity hU
      (show ContinuousOn (fun y => f y - b) U from hf.sub continuousOn_const)
      (fun y hy z hz hyz => hfi hy hz
        (add_right_cancel (by simpa only [sub_eq_add_neg] using hyz))) x =
      embeddingOrientationParity hU hf hfi x := by
  unfold embeddingOrientationParity
  simp only [sub_sub_sub_cancel_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.embeddingOrientationParity_sub_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.embeddingOrientationParity_sub_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.embeddingOrientationParity_sub_const ``Submission.DifferentialGeometry.LocalDegree.embeddingOrientationParity_sub_const

end DifferentialGeometry.LocalDegree
