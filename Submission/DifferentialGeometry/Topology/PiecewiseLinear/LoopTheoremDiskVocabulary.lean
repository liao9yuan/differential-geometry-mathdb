/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

def IsLoopTheoremDisk (Kimg N' BdX Δ : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
    IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧ Δ ⊆ interior N' \ Kimg ∧
    Δ ∩ BdX = r '' stdSimplexBoundary 2 ∧
    ∃ hb : r '' stdSimplexBoundary 2 ⊆ BdX,
      ¬ (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
        C(r '' stdSimplexBoundary 2, BdX)).Nullhomotopic

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsLoopTheoremDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsLoopTheoremDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsLoopTheoremDisk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsLoopTheoremDisk

def HasNoHandleLoopTheoremDisk (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (N' : Set (EuclideanSpace ℝ (Fin 3)))
    (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (X : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ v ∈ K.vertices, ∀ Δ : Set (EuclideanSpace ℝ (Fin 3)),
    IsLoopTheoremDisk (h '' K.space) N' (frontier X) Δ → ¬ Δ ⊆ Cpp v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.HasNoHandleLoopTheoremDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.HasNoHandleLoopTheoremDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.HasNoHandleLoopTheoremDisk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.HasNoHandleLoopTheoremDisk

end DifferentialGeometry.Topology.PiecewiseLinear
