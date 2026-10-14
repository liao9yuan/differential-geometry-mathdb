/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Endgame
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise352InwardPushProof
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.OpenSourceReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem moise352_three_of_open : Moise352Open.{u} 3 → Moise352.{u} 3 :=
  moise352_of_inwardPush_of_open moise352InwardPush_three

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise352_three_of_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise352_three_of_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise352_three_of_open ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise352_three_of_open

theorem plApproximationManifold_three_of_open :
    Moise352Open.{u} 3 → PLApproximationManifold.{u} 3 :=
  fun hopen => plApproximationManifold_three_of_moise352 (moise352_three_of_open hopen)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three_of_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three_of_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three_of_open ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three_of_open

end DifferentialGeometry.Topology.PiecewiseLinear
