/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsSmoothHandleStage (Y : Type*) [TopologicalSpace Y] (Bd : Set Y) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace (EuclideanHalfSpace 3) M),
    IsManifold (𝓡∂ 3) ∞ M ∧ T2Space M ∧ CompactSpace M ∧
      ∃ h : Y ≃ₜ M, h '' Bd = (𝓡∂ 3).boundary M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage

theorem isSmoothHandleStage_of_isEmpty (Y : Type*) [TopologicalSpace Y] [IsEmpty Y] (Bd : Set Y) :
    IsSmoothHandleStage Y Bd := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) Empty := ChartedSpace.empty _ Empty
  refine ⟨Empty, inferInstance, inferInstance, IsManifold.empty _, inferInstance,
    inferInstance, Homeomorph.empty, ?_⟩
  exact Set.ext fun x => isEmptyElim x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_of_isEmpty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_of_isEmpty

theorem IsSmoothHandleStage.transport {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {Bd : Set Y} (hY : IsSmoothHandleStage Y Bd) (e : Y ≃ₜ Z) :
    IsSmoothHandleStage Z (e '' Bd) := by
  obtain ⟨M, iT, iC, hM, hT2, hc, f, hf⟩ := hY
  refine ⟨M, iT, iC, hM, hT2, hc, e.symm.trans f, ?_⟩
  rw [Set.image_image]
  simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  exact hf

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage.transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage.transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage.transport ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSmoothHandleStage.transport

end DifferentialGeometry.Topology.PiecewiseLinear
