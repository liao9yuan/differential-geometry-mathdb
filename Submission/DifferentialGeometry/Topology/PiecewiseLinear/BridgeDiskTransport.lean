/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskArc
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsBridgeDisk.image {C A B : Set E} {D : Set F} {a b : E}
    (h : IsBridgeDisk C A B a b) {f : E → F} (hf : IsPLHomeomorphOn f C D)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hC : IsClosed C) (hD : IsClosed D) :
    IsBridgeDisk D (f '' A) (f '' B) (f a) (f b) := by
  obtain ⟨q, hq, hBC, hbase, htrace, hq0, hq1⟩ := h
  have hB : IsPLBall 2 B := ⟨q, hq⟩
  have hfB := hf.restrict hB.isPolyhedron hBC
  refine ⟨f ∘ q, hq.trans hfB, (_root_.Set.image_mono hBC).trans hf.image_eq.subset, ?_, ?_, ?_, ?_⟩
  · rw [_root_.Set.image_comp, hbase]
  · rw [← hf.image_frontier hdim hC hD,
      ← hf.bijOn.injOn.image_inter hBC hC.frontier_subset, htrace, _root_.Set.image_comp]
  · exact congrArg f hq0
  · exact congrArg f hq1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.image

end DifferentialGeometry.Topology.PiecewiseLinear
