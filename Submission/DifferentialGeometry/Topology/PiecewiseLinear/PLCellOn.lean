/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Transition361

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

def IsPLCellOn (d : ℕ) (S B : Set M) : Prop :=
  ∃ (P : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3))
    (u : EuclideanSpace ℝ (Fin 3) → M),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin (d + 1))) P ∧ IsPLHomeomorphInto 3 u P ∧
      S = u '' P ∧ B = u '' (r '' stdSimplexBoundary d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn

theorem IsPLCellOn.isCompact {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) : IsCompact S := by
  obtain ⟨P, r, u, hr, hu, hcell, -⟩ := hS
  rw [hcell]
  exact ((IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact).image_of_continuousOn hu.continuousOn

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isCompact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isCompact

theorem IsPLCellOn.nonempty {d : ℕ} {S B : Set M} (hS : IsPLCellOn d S B) : S.Nonempty := by
  obtain ⟨P, r, u, hr, -, hcell, -⟩ := hS
  rw [hcell]
  exact (IsPLBall.nonempty ⟨r, hr⟩).image u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nonempty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.nonempty

end DifferentialGeometry.Topology.PiecewiseLinear
