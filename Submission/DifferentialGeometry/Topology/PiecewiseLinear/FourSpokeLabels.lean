/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeSquareWitness
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfPlaneRectangle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def fourSpokeLabel : Fin 4 ≃ Bool × Bool where
  toFun i := match i with
    | 0 => (_root_.Bool.false, _root_.Bool.true)
    | 1 => (_root_.Bool.true, _root_.Bool.true)
    | 2 => (_root_.Bool.false, _root_.Bool.false)
    | 3 => (_root_.Bool.true, _root_.Bool.false)
  invFun p := if p.1 then if p.2 then 1 else 3 else if p.2 then 0 else 2
  left_inv i := by fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨b, s⟩; cases b <;> cases s <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel

theorem fourSpokeLabel_flip (i : Fin 4) :
    fourSpokeLabel (fourSpokeFlipPerm i) = (!(fourSpokeLabel i).1, (fourSpokeLabel i).2) := by
  fin_cases i <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_flip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_flip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_flip ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_flip

theorem fourSpokeLabel_add_two (i : Fin 4) :
    fourSpokeLabel (i + 2) = ((fourSpokeLabel i).1, !(fourSpokeLabel i).2) := by
  fin_cases i <;> rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_add_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_add_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_add_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLabel_add_two

theorem mem_crossHalfPlane_iff_label (i : Fin 4) (p : (ℝ × ℝ) × ℝ) :
    p ∈ crossHalfPlane i ↔
      (if (fourSpokeLabel i).1 then p.1.1 = 0 else p.1.2 = 0) ∧
      (if (fourSpokeLabel i).2 then
        0 ≤ (if (fourSpokeLabel i).1 then p.1.2 else p.1.1)
      else (if (fourSpokeLabel i).1 then p.1.2 else p.1.1) ≤ 0) := by
  fin_cases i <;> simp only [fourSpokeLabel, Equiv.coe_fn_mk, Bool.false_eq_true,
    if_false, if_true] <;> constructor
  all_goals try
    rintro ⟨a, ha, hpa⟩
    simp only [fourSpokeModelLeaf, Prod.smul_mk, smul_eq_mul, mul_one, _root_.MulZeroClass.mul_zero,
      mul_neg_one] at hpa
    rw [hpa]
    simpa using ha
  · rintro ⟨hy, hx⟩
    exact ⟨p.1.1, hx, by ext <;> simp [fourSpokeModelLeaf, hy]⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p.1.2, hy, by ext <;> simp [fourSpokeModelLeaf, hx]⟩
  · rintro ⟨hy, hx⟩
    exact ⟨-p.1.1, neg_nonneg.mpr hx, by ext <;> simp [fourSpokeModelLeaf, hy]⟩
  · rintro ⟨hx, hy⟩
    exact ⟨-p.1.2, neg_nonneg.mpr hy, by ext <;> simp [fourSpokeModelLeaf, hx]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlane_iff_label then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlane_iff_label"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlane_iff_label ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_crossHalfPlane_iff_label

end DifferentialGeometry.Topology.PiecewiseLinear
