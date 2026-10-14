/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceLocality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.sdiff_of_disjoint {L T C : Set E3}
    (h : HasFiniteCollaredTrace L T) (hC : IsClosed C) (hCT : Disjoint C T)
    (hrem : IsPolyhedron (L \ C)) : HasFiniteCollaredTrace (L \ C) T := by
  apply h.of_locally_eq hrem hC.isOpen_compl (fun x hx => disjoint_left.mp hCT.symm hx)
  ext x
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hx.2⟩, hx.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.sdiff_of_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.sdiff_of_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.sdiff_of_disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasFiniteCollaredTrace.sdiff_of_disjoint

end DifferentialGeometry.Topology.PiecewiseLinear
