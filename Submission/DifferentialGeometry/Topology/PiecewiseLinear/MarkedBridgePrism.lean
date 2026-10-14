/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskPrism
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StandardPrismCapAdjustment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V2" => Fin 3 → ℝ
local notation "Δ" => stdSimplex ℝ (Fin 3)
local notation "p" => stdCenter 1

theorem exists_marked_prism_of_isBridgeDisk
    {C A B D0 D1 : Set E3}
    (hC : IsPLBall 3 C)
    (hD0 : D0 ⊆ frontier C) (hD1 : D1 ⊆ frontier C)
    (hdis : Disjoint D0 D1)
    {r0 r1 : V2 → E3}
    (hr0 : IsPLHomeomorphOn r0 Δ D0)
    (hr1 : IsPLHomeomorphOn r1 Δ D1)
    (hb : IsBridgeDisk C A B (r0 p) (r1 p)) :
    ∃ ρ : V2 × ℝ → E3,
      IsPLHomeomorphOn ρ (Δ ×ˢ _root_.Set.Icc (0 : ℝ) 1) C ∧
      ρ '' (Δ ×ˢ {(0 : ℝ)}) = D0 ∧
      ρ '' (Δ ×ˢ {(1 : ℝ)}) = D1 ∧
      ρ (p, 0) = r0 p ∧ ρ (p, 1) = r1 p ∧
      ρ '' ({p} ×ˢ _root_.Set.Icc (0 : ℝ) 1) = A := by
  obtain ⟨τ, hτ, hτA, hτ0, hτ1⟩ := hb.exists_prism_axis hC
  obtain ⟨ρ, hρ, hρ0, hρ1, hρaxis⟩ :=
    hτ.exists_prism_cap_images_preserving_stdCenter hD0 hD1 hdis hr0 hr1 hτ0 hτ1
  refine ⟨ρ, hρ, hρ0, hρ1, (hρaxis 0 (by norm_num)).trans hτ0,
    (hρaxis 1 (by norm_num)).trans hτ1, ?_⟩
  have heq : _root_.Set.EqOn ρ τ ({p} ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hxp : x = p := hx
    subst x
    exact hρaxis t ht
  exact heq.image_eq.trans hτA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_prism_of_isBridgeDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_prism_of_isBridgeDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_prism_of_isBridgeDisk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_marked_prism_of_isBridgeDisk

end DifferentialGeometry.Topology.PiecewiseLinear
