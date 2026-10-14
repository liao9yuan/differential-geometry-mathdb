/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ApproximationManifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise352OfOpen
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLSmoothingCompact
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34Terminal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem moise352Open : Moise352Open.{u} 3 :=
  moise352Open_of_section34CellDiagram section34CellDiagram

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise352Open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise352Open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise352Open ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise352Open

theorem moise352 : Moise352.{u} 3 :=
  moise352_three_of_open moise352Open

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise352 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise352"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise352 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise352

theorem plApproximationManifold_three : PLApproximationManifold.{u} 3 :=
  plApproximationManifold_three_of_open moise352Open

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plApproximationManifold_three

theorem plApproximation_three : PLApproximation.{u} 3 :=
  plApproximation_of_plApproximationManifold plApproximationManifold_three

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plApproximation_three

theorem plSmoothingCompact_three : PLSmoothingCompact.{u} 3 :=
  plSmoothingCompact_of_plSmoothingModelCompact plSmoothingModelCompact_three

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.plSmoothingCompact_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.plSmoothingCompact_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.plSmoothingCompact_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.plSmoothingCompact_three

theorem exists_isManifold_three {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := C
      IsManifold (𝓡 3) ∞ M :=
  exists_isManifold_of_plApproximation_of_plSmoothingCompact plApproximation_three
    plSmoothingCompact_three

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isManifold_three

end DifferentialGeometry.Topology.PiecewiseLinear
