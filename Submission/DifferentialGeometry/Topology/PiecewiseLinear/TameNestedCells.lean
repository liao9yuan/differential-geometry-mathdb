/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphereNesting
import Submission.DifferentialGeometry.Topology.ClosedBallImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def BicollaredCellComplementConnected : Prop :=
  ∀ C : Set (EuclideanSpace ℝ (Fin 3)),
    IsTopologicalCell 3 C → IsBicollared (frontier C) → IsConnected Cᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.BicollaredCellComplementConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.BicollaredCellComplementConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.BicollaredCellComplementConnected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.BicollaredCellComplementConnected

theorem bicollared_cell_complement_connected : BicollaredCellComplementConnected := by
  intro C ⟨φ⟩ hbi
  exact isConnected_compl_of_homeomorphClosedBall_of_isBicollared
    (by rw [← Module.finrank_eq_rank']; norm_num) φ hbi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bicollared_cell_complement_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bicollared_cell_complement_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bicollared_cell_complement_connected ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bicollared_cell_complement_connected

def Moise305Tame : Prop :=
  ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin 3)),
    IsTopologicalCell 3 C₁ → IsTopologicalCell 3 C₂ → C₁ ⊆ interior C₂ →
    IsSphericalShell (closure (C₂ \ C₁)) (frontier C₁) (frontier C₂) →
    IsBicollared (frontier C₂) →
    ∃ C, IsPLBall 3 C ∧ C₁ ⊆ interior C ∧ C ⊆ interior C₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.Moise305Tame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.Moise305Tame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.Moise305Tame ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.Moise305Tame

theorem moise305_tame_of_moise304 (h304 : Moise304) : Moise305Tame := by
  intro C₁ C₂ ⟨φ₁⟩ ⟨φ₂⟩ _ hshell hbi
  obtain ⟨B, hB, hBX, hsep⟩ := h304 _ _ _ hshell
  have hconn₁ : IsConnected C₁ := by
    have : ConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      isConnected_iff_connectedSpace.mp (Metric.isConnected_closedBall (by norm_num))
    rw [← range_closedBallParam φ₁]
    exact isConnected_range (continuous_closedBallParam φ₁)
  obtain ⟨D, hD, -, h₁D, hD₂⟩ := hB.exists_isPLBall_between_of_separates
    (isCompact_of_homeomorphClosedBall φ₁).isClosed
    (isCompact_of_homeomorphClosedBall φ₂) hconn₁
    (bicollared_cell_complement_connected C₂ ⟨φ₂⟩ hbi).isPreconnected hBX hsep
  exact ⟨D, hD, h₁D, hD₂⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.moise305_tame_of_moise304 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.moise305_tame_of_moise304"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.moise305_tame_of_moise304 ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.moise305_tame_of_moise304

end DifferentialGeometry.Topology.PiecewiseLinear
