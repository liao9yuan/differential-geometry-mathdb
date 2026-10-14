/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.Moise252Producer
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section32PseudoCell
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section33Approximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeApproximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34Compact

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem moise331OnTube : Moise331OnTube :=
  moise331OnTube_of_moise323_of_moise324_of_moise264Orientable moise323 moise324
    moise264Orientable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise331OnTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise331OnTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise331OnTube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise331OnTube

theorem moise331 : Moise331 :=
  Moise331OnTube.moise331 moise331OnTube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise331 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise331"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise331 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise331

theorem moise341 : Moise341 :=
  moise341_of_onNeighborhood moise331OnTube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise341 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise341"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise341 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise341

end DifferentialGeometry.Topology.PiecewiseLinear
