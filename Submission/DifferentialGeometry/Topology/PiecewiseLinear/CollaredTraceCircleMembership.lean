/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTraceMonotonicity
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceUnion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.mem_traceCircles_of_isPLSphere {L T G : Set E3}
    (hL : HasFiniteCollaredTrace L T) (hG : IsPLSphere 1 G) (hsub : G ⊆ L ∩ T) :
    G ∈ traceCircles L T := by
  obtain ⟨x, hx⟩ := hG.nonempty
  have hGT : G ⊆ T := hsub.trans _root_.Set.inter_subset_right
  have hself : G ∈ traceCircles G T := by
    refine ⟨x, ⟨hx, hGT hx⟩, ?_, hG⟩
    apply Subset.antisymm
    · exact hG.isConnected.isPreconnected.subset_connectedComponentIn hx
        (fun y hy => ⟨hy, hGT hy⟩)
    · exact (connectedComponentIn_subset _ _).trans _root_.Set.inter_subset_left
  exact traceCircles_subset_of_inter_subset hL.traceCover
    (fun y hy => hsub hy.1) hself

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.mem_traceCircles_of_isPLSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.mem_traceCircles_of_isPLSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.mem_traceCircles_of_isPLSphere ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.mem_traceCircles_of_isPLSphere

end DifferentialGeometry.Topology.PiecewiseLinear
