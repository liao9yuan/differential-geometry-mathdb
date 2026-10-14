/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskEquivalence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StandardMarkedBridge

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V2" => Fin 3 → ℝ

theorem IsBridgeDisk.exists_prism_axis
    {C A B : Set E3} {a b : E3} (h : IsBridgeDisk C A B a b) (hC : IsPLBall 3 C) :
    ∃ ρ : V2 × ℝ → E3,
      IsPLHomeomorphOn ρ (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) C ∧
      ρ '' ({stdCenter 1} ×ˢ _root_.Set.Icc (0 : ℝ) 1) = A ∧
      ρ (stdCenter 1, 0) = a ∧ ρ (stdCenter 1, 1) = b := by
  obtain ⟨C₀, B₀, ρ₀, hC₀, hρ₀, hb₀⟩ := exists_isBridgeDisk_prism_axis
  obtain ⟨G, hG, hGA, hGa, hGb⟩ := hb₀.exists_isPLHomeomorphOn_map_arc h hC₀ hC
  refine ⟨G ∘ ρ₀, hρ₀.trans hG, ?_, hGa, hGb⟩
  rw [_root_.Set.image_comp]
  exact hGA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_prism_axis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_prism_axis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_prism_axis ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_prism_axis

end DifferentialGeometry.Topology.PiecewiseLinear
