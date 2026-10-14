/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionInDouble
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReductionOrientableProducer
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DescentStepOrientable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise304 : Moise304 :=
  moise304_of_generalPositionBuffered_of_descentStepOrientable generalPositionInDoubleBuffered
    descentStepOrientableStatement

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise304 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise304"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise304 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise304

theorem moise305Tame : Moise305Tame :=
  moise305_tame_of_moise304 moise304

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise305Tame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise305Tame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise305Tame ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise305Tame

end DifferentialGeometry.Topology.PiecewiseLinear
