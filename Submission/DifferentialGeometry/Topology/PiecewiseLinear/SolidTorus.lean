/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsTopologicalSolidTorus {E : Type u} [TopologicalSpace E] (S : Set E) : Prop :=
  Nonempty (S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsTopologicalSolidTorus

end DifferentialGeometry.Topology.PiecewiseLinear
