/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchEndChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLBoundaryTubeProducer_double
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    IsPLBoundaryTubeProducer (double 3 K).space :=
  isPLBoundaryTubeProducer_of_exists_endChart (double 3 K)
    (isCombinatorialManifold_double_succ_succ K hK)
    (exists_endChart_of_mem_boundary (double 3 K) (isCombinatorialManifold_double_succ_succ K hK))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundaryTubeProducer_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundaryTubeProducer_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundaryTubeProducer_double ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBoundaryTubeProducer_double

end DifferentialGeometry.Topology.PiecewiseLinear
