import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Analysis

theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  have hden := (Real.smoothTransition.pos_denom x).ne'
  simp only [Real.smoothTransition, sub_sub_cancel]
  rw [add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x)]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothTransition_one_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothTransition_one_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothTransition_one_sub ``Submission.DifferentialGeometry.Analysis.smoothTransition_one_sub

private theorem expNegInvGlue_lt_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    expNegInvGlue x < expNegInvGlue y := by
  simp only [expNegInvGlue, if_neg hx.not_ge, if_neg (hx.trans hxy).not_ge]
  apply Real.exp_lt_exp.mpr
  simpa only [neg_div, one_div] using neg_lt_neg (one_div_lt_one_div_of_lt hx hxy)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.expNegInvGlue_lt_of_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.expNegInvGlue_lt_of_pos target :: scope.openDecls } }

theorem smoothTransition_strictMonoOn :
    StrictMonoOn Real.smoothTransition (_root_.Set.Icc 0 1) := by
  intro x hx y hy hxy
  rcases hx.1.eq_or_lt with hx0 | hx0
  · rw [← hx0, Real.smoothTransition.zero]
    exact Real.smoothTransition.pos_of_pos (hx0 ▸ hxy)
  rcases hy.2.eq_or_lt with hy1 | hy1
  · rw [hy1, Real.smoothTransition.one]
    exact Real.smoothTransition.lt_one_of_lt_one (hy1 ▸ hxy)
  simp only [Real.smoothTransition]
  rw [div_lt_div_iff₀ (Real.smoothTransition.pos_denom x)
    (Real.smoothTransition.pos_denom y)]
  simp only [mul_add, mul_comm (expNegInvGlue x) (expNegInvGlue y), add_lt_add_iff_left]
  calc
    expNegInvGlue x * expNegInvGlue (1 - y) <
        expNegInvGlue y * expNegInvGlue (1 - y) :=
      mul_lt_mul_of_pos_right (expNegInvGlue_lt_of_pos hx0 hxy)
        (expNegInvGlue.pos_of_pos (sub_pos.mpr hy1))
    _ ≤ expNegInvGlue y * expNegInvGlue (1 - x) :=
      mul_le_mul_of_nonneg_left (expNegInvGlue.monotone (by linarith))
        (expNegInvGlue.nonneg y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothTransition_strictMonoOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothTransition_strictMonoOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothTransition_strictMonoOn ``Submission.DifferentialGeometry.Analysis.smoothTransition_strictMonoOn

theorem integral_smoothTransition :
    (∫ x in (0 : ℝ)..1, Real.smoothTransition x) = 1 / 2 := by
  have hi : IntervalIntegrable Real.smoothTransition MeasureTheory.volume 0 1 :=
    Real.smoothTransition.continuous.intervalIntegrable 0 1
  have href : (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x)) =
      ∫ x in (0 : ℝ)..1, Real.smoothTransition x := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left Real.smoothTransition 1 (a := 0) (b := 1)
  simp_rw [smoothTransition_one_sub] at href
  rw [intervalIntegral.integral_sub intervalIntegrable_const hi] at href
  norm_num at href
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_smoothTransition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_smoothTransition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_smoothTransition ``Submission.DifferentialGeometry.Analysis.integral_smoothTransition

theorem integral_smoothTransition_one_sub :
    (∫ x in (0 : ℝ)..1, Real.smoothTransition (1 - x)) = 1 / 2 := by
  simpa only [sub_self, sub_zero, integral_smoothTransition] using
    intervalIntegral.integral_comp_sub_left Real.smoothTransition 1 (a := 0) (b := 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_smoothTransition_one_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_smoothTransition_one_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_smoothTransition_one_sub ``Submission.DifferentialGeometry.Analysis.integral_smoothTransition_one_sub

end DifferentialGeometry.Analysis
