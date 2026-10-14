import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


namespace Real
open _root_.Real

open _root_.Real in
theorem min_sqrt_sub_le_sqrt_sub_max_half {δ tau a : ℝ} (h : δ ≤ tau) :
    min (_root_.Real.sqrt δ - a) (_root_.Real.sqrt δ / 2) ≤ _root_.Real.sqrt tau - _root_.Max.max a (_root_.Real.sqrt tau / 2) := by
  have hsqrt := _root_.Real.sqrt_le_sqrt h
  rcases le_total a (_root_.Real.sqrt tau / 2) with ha | ha
  · rw [max_eq_right ha]
    have hm := min_le_right (_root_.Real.sqrt δ - a) (_root_.Real.sqrt δ / 2)
    linarith
  · rw [max_eq_left ha]
    exact (min_le_left _ _).trans (sub_le_sub_right hsqrt a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.min_sqrt_sub_le_sqrt_sub_max_half then
    throwError "Refusing to shadow existing declaration Real.min_sqrt_sub_le_sqrt_sub_max_half"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.min_sqrt_sub_le_sqrt_sub_max_half ``Submission.Real.min_sqrt_sub_le_sqrt_sub_max_half

open _root_.Real in
theorem min_sqrt_sub_half_pos {δ a : ℝ} (hδ : 0 < δ) (ha : a < _root_.Real.sqrt δ) :
    0 < _root_.Min.min (_root_.Real.sqrt δ - a) (_root_.Real.sqrt δ / 2) :=
  lt_min (sub_pos.mpr ha) (half_pos (_root_.Real.sqrt_pos.mpr hδ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.min_sqrt_sub_half_pos then
    throwError "Refusing to shadow existing declaration Real.min_sqrt_sub_half_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.min_sqrt_sub_half_pos ``Submission.Real.min_sqrt_sub_half_pos

open _root_.Real in
theorem sqrt_midpoint_one_lt {δ : ℝ} (hδ : 1 < δ) :
    sqrt ((1 + δ) / 2) < _root_.Real.sqrt δ := by
  apply _root_.Real.sqrt_lt_sqrt
  · linarith
  · linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.sqrt_midpoint_one_lt then
    throwError "Refusing to shadow existing declaration Real.sqrt_midpoint_one_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.sqrt_midpoint_one_lt ``Submission.Real.sqrt_midpoint_one_lt

open _root_.Real in
theorem one_sub_sq_mem_Icc_of_mem_final_tail
    {δ T tau s : ℝ} (hδ : 1 < δ) (htau : tau ∈ Set.Icc δ T)
    (hs : s ∈ Set.Icc (_root_.Max.max (_root_.Real.sqrt ((1 + δ) / 2)) (_root_.Real.sqrt tau / 2)) (_root_.Real.sqrt tau)) :
    1 - s ^ 2 ∈ Set.Icc (1 - T) (-(δ - 1) / 2) := by
  have hδpos : 0 < δ := zero_lt_one.trans hδ
  have htaupos : 0 < tau := hδpos.trans_le htau.1
  have hmidpos : 0 ≤ (1 + δ) / 2 := by linarith
  have hlo : _root_.Real.sqrt ((1 + δ) / 2) ≤ s := (le_max_left _ _).trans hs.1
  have hs0 : 0 ≤ s := (_root_.Real.sqrt_nonneg _).trans hlo
  have hsquareLower := mul_self_le_mul_self (_root_.Real.sqrt_nonneg ((1 + δ) / 2)) hlo
  have hsquareUpper := mul_self_le_mul_self hs0 hs.2
  have hmid := _root_.Real.sq_sqrt hmidpos
  have htop := _root_.Real.sq_sqrt htaupos.le
  constructor <;> nlinarith only [hsquareLower, hsquareUpper, hmid, htop, htau.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.one_sub_sq_mem_Icc_of_mem_final_tail then
    throwError "Refusing to shadow existing declaration Real.one_sub_sq_mem_Icc_of_mem_final_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.one_sub_sq_mem_Icc_of_mem_final_tail ``Submission.Real.one_sub_sq_mem_Icc_of_mem_final_tail

end Real
