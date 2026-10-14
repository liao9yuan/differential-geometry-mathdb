/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
def IsCombinatorialSolidTorus (S : Set E) : Prop :=
  IsTopologicalSolidTorus S ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ C : Fin n → Geometry.SimplicialComplex ℝ E,
      (∀ i, (C i).faces.Finite) ∧ (⋃ i, (C i).space) = S ∧
      (∀ i, IsPLBall 3 (C i).space) ∧
      ∀ i j, i ≠ j →
        (((C i).space ∩ (C j).space).Nonempty ↔ (SimpleGraph.cycleGraph n).Adj i j) ∧
        ((SimpleGraph.cycleGraph n).Adj i j →
          IsPLBall 2 ((C i).space ∩ (C j).space) ∧
          (C i).space ∩ (C j).space ⊆ (boundaryComplex 3 (C i)).space ∧
          (C i).space ∩ (C j).space ⊆ (boundaryComplex 3 (C j)).space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialSolidTorus

end DifferentialGeometry.Topology.PiecewiseLinear
