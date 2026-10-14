/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ExtendedLoopTheoremOrientable
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionInDouble
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CoverReductionOrientableProducer
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DescentStepOrientable
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoOrientable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise252 : Moise252 :=
  moise252_of_lemmaTwoOrientable
    (lemmaTwoBufferedOrientableStatement_of_generalPosition_of_descentStepOrientable
      generalPositionInDoubleBuffered descentStepOrientableStatement)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise252 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise252"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise252 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise252

theorem moise264Orientable : Moise264Orientable :=
  moise264_orientable moise252

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise264Orientable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise264Orientable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise264Orientable ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise264Orientable

end DifferentialGeometry.Topology.PiecewiseLinear
