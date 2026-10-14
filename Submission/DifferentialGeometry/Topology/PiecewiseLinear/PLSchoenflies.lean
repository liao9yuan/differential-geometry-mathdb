/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Schoenflies
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SchoenfliesFoundations

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.isSimplyEmbedded {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) : IsSimplyEmbedded S :=
  isSimplyEmbedded_of_isPLSphere_two schoenflies_input hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isSimplyEmbedded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isSimplyEmbedded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isSimplyEmbedded ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.isSimplyEmbedded

theorem IsPLSphere.exists_isPLBall_frontier_eq {S : Set (EuclideanSpace ℝ (Fin 3))}
    (hS : IsPLSphere 2 S) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 B ∧ frontier B = S ∧ Bornology.IsBounded B :=
  exists_isPLBall_of_isPLSphere_two schoenflies_input hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_isPLBall_frontier_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_isPLBall_frontier_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_isPLBall_frontier_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere.exists_isPLBall_frontier_eq

theorem forall_isSimplyEmbedded_of_isPLSphere_two :
    ∀ S : Set (EuclideanSpace ℝ (Fin 3)), IsPLSphere 2 S → IsSimplyEmbedded S :=
  fun _ hS => hS.isSimplyEmbedded

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.forall_isSimplyEmbedded_of_isPLSphere_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.forall_isSimplyEmbedded_of_isPLSphere_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.forall_isSimplyEmbedded_of_isPLSphere_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.forall_isSimplyEmbedded_of_isPLSphere_two

end DifferentialGeometry.Topology.PiecewiseLinear
