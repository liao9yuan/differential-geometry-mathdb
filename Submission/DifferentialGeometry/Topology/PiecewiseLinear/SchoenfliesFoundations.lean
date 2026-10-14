/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConvexStraightening
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskGluing
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FreeDiskCell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem schoenflies_input : SchoenfliesInput where
  isSimplyEmbedded_frontier_of_convex _ hconv hball :=
    PiecewiseLinear.isSimplyEmbedded_frontier_of_convex hconv hball
  isSimplyEmbedded_frontier_coneComplex L _ hp hfinite hL := by
    let _ : Finite L.faces := hfinite.to_subtype
    exact PiecewiseLinear.isSimplyEmbedded_frontier_coneComplex L hp hL
  isSimplyEmbedded_union_sdiff_diskInterior _ _ _ _ ℓ _ hS₁ hS₂ hq hℓ hDr hD :=
    isSimplyEmbedded_union_sdiff_diskInterior_of_subset_fiber hS₁ hS₂ hq ℓ hℓ hDr hD
  exists_two_free_disk_cells _ _ h hmore := h.exists_two_free_disk_cells hmore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.schoenflies_input then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.schoenflies_input"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.schoenflies_input ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.schoenflies_input

end DifferentialGeometry.Topology.PiecewiseLinear
