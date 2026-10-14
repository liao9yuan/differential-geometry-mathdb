/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace Real.smoothTransition
open _root_.Real _root_.Real.smoothTransition

open _root_.Real _root_.Real.smoothTransition in
theorem integral_zero_one : (∫ x in (0 : ℝ)..1, _root_.Real.smoothTransition x) = 1 / 2 := by
  have hcont : IntervalIntegrable _root_.Real.smoothTransition MeasureTheory.volume 0 1 :=
    smoothTransition.continuous.intervalIntegrable 0 1
  have hchange :
      (∫ x in (0 : ℝ)..1, _root_.Real.smoothTransition (1 - x)) =
        ∫ x in (0 : ℝ)..1, _root_.Real.smoothTransition x := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left
        (f := _root_.Real.smoothTransition) (a := (0 : ℝ)) (b := 1) 1)
  simp_rw [one_sub] at hchange
  rw [intervalIntegral.integral_sub intervalIntegrable_const hcont] at hchange
  norm_num at hchange ⊢
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.integral_zero_one then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.integral_zero_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.integral_zero_one ``Submission.Real.smoothTransition.integral_zero_one

open _root_.Real _root_.Real.smoothTransition in
theorem integral_comp_sub_div (a b : ℝ) :
    (∫ x in a..b, _root_.Real.smoothTransition ((x - a) / (b - a))) = (b - a) / 2 := by
  by_cases hab : b = a
  · subst b
    simp
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab
    rw [intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => _root_.Real.smoothTransition (x / (b - a))) a]
    rw [intervalIntegral.integral_comp_div _root_.Real.smoothTransition hba]
    simp only [sub_self, zero_div, div_self hba, integral_zero_one, smul_eq_mul]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.integral_comp_sub_div then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.integral_comp_sub_div"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.integral_comp_sub_div ``Submission.Real.smoothTransition.integral_comp_sub_div

open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology

open _root_.Real _root_.Real.smoothTransition in
theorem contDiff_one_sub_mul_sub (a b c : ℝ) :
    ContDiff ℝ ∞ (fun t => (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t)) :=
  (contDiff_const.sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a)))).mul
    (contDiff_const.sub contDiff_id)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.contDiff_one_sub_mul_sub then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.contDiff_one_sub_mul_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.contDiff_one_sub_mul_sub ``Submission.Real.smoothTransition.contDiff_one_sub_mul_sub

open _root_.Real _root_.Real.smoothTransition in
theorem one_sub_mul_sub_eq_sub {a b c t : ℝ} (hab : a < b) (ht : t ≤ a) :
    (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t) = c - t := by
  rw [_root_.Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
    (sub_nonneg.mpr hab.le)), sub_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.one_sub_mul_sub_eq_sub then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.one_sub_mul_sub_eq_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.one_sub_mul_sub_eq_sub ``Submission.Real.smoothTransition.one_sub_mul_sub_eq_sub

open _root_.Real _root_.Real.smoothTransition in
theorem one_sub_mul_sub_eq_zero {a b c t : ℝ} (hab : a < b) (ht : b ≤ t) :
    (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t) = 0 := by
  rw [_root_.Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), sub_self, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.one_sub_mul_sub_eq_zero then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.one_sub_mul_sub_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.one_sub_mul_sub_eq_zero ``Submission.Real.smoothTransition.one_sub_mul_sub_eq_zero

open _root_.Real _root_.Real.smoothTransition in
theorem one_sub_mul_sub_nonneg {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) (t : ℝ) :
    0 ≤ (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t) := by
  by_cases ht : b ≤ t
  · rw [one_sub_mul_sub_eq_zero hab ht]
  · exact mul_nonneg (sub_nonneg.mpr (_root_.Real.smoothTransition.le_one _))
      (sub_nonneg.mpr ((le_of_not_ge ht).trans hbc))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.one_sub_mul_sub_nonneg then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.one_sub_mul_sub_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.one_sub_mul_sub_nonneg ``Submission.Real.smoothTransition.one_sub_mul_sub_nonneg

open _root_.Real _root_.Real.smoothTransition in
theorem antitone_one_sub_mul_sub {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) :
    Antitone (fun t => (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t)) := by
  intro x y hxy
  dsimp only
  by_cases hy : b ≤ y
  · rw [one_sub_mul_sub_eq_zero hab hy]
    exact one_sub_mul_sub_nonneg hab hbc x
  · have hχ := Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy a)
        (sub_nonneg.mpr hab.le))
    exact mul_le_mul (sub_le_sub_left hχ 1) (sub_le_sub_left hxy c)
      (sub_nonneg.mpr ((le_of_not_ge hy).trans hbc)) (sub_nonneg.mpr (_root_.Real.smoothTransition.le_one _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.antitone_one_sub_mul_sub then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.antitone_one_sub_mul_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.antitone_one_sub_mul_sub ``Submission.Real.smoothTransition.antitone_one_sub_mul_sub

open _root_.Real _root_.Real.smoothTransition in
theorem strictAntiOn_one_sub_mul_sub {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) :
    StrictAntiOn (fun t => (1 - Real.smoothTransition ((t - a) / (b - a))) * (c - t))
      (_root_.Set.Iio b) := by
  intro x _ y hy hxy
  dsimp only
  change y < b at hy
  have hχ := Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy.le a)
      (sub_nonneg.mpr hab.le))
  have hyχ : 0 < 1 - Real.smoothTransition ((y - a) / (b - a)) :=
    sub_pos.mpr (_root_.Real.smoothTransition.lt_one_of_lt_one ((div_lt_one (sub_pos.mpr hab)).mpr (by linarith)))
  exact (mul_lt_mul_of_pos_left (sub_lt_sub_left hxy c) hyχ).trans_le
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hχ 1)
      (sub_nonneg.mpr (hxy.le.trans (hy.le.trans hbc))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.strictAntiOn_one_sub_mul_sub then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.strictAntiOn_one_sub_mul_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.strictAntiOn_one_sub_mul_sub ``Submission.Real.smoothTransition.strictAntiOn_one_sub_mul_sub

open _root_.Real _root_.Real.smoothTransition in
theorem deriv_one_sub_mul_sub_nonpos {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) (t : ℝ) :
    deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t ≤ 0 :=
  (antitone_one_sub_mul_sub hab hbc).deriv_nonpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.deriv_one_sub_mul_sub_nonpos then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.deriv_one_sub_mul_sub_nonpos"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.deriv_one_sub_mul_sub_nonpos ``Submission.Real.smoothTransition.deriv_one_sub_mul_sub_nonpos

open _root_.Real _root_.Real.smoothTransition in
theorem deriv_one_sub_mul_sub_neg {a b c t : ℝ} (hab : a < b) (hbc : b ≤ c) (ht : t < b) :
    deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t < 0 := by
  have hχ := (((show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff
    ).differentiable (by simp) _).hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const a).div_const (b - a))
  have hA := (hχ.const_sub 1).mul ((hasDerivAt_id t).const_sub c)
  have heq : deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t =
      -(deriv Real.smoothTransition ((t - a) / (b - a)) * (1 / (b - a))) * (c - t) +
        (1 - Real.smoothTransition ((t - a) / (b - a))) * (-1) := by
    simpa only [Function.comp_def, id_eq, Pi.mul_def] using hA.deriv
  rw [heq]
  have hd : 0 ≤ deriv Real.smoothTransition ((t - a) / (b - a)) * (1 / (b - a)) :=
    mul_nonneg Real.smoothTransition.monotone.deriv_nonneg (by positivity)
  have hct : 0 ≤ c - t := sub_nonneg.mpr (ht.le.trans hbc)
  have hχlt : Real.smoothTransition ((t - a) / (b - a)) < 1 :=
    _root_.Real.smoothTransition.lt_one_of_lt_one ((div_lt_one (sub_pos.mpr hab)).mpr (by linarith))
  nlinarith [mul_nonneg hd hct]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.deriv_one_sub_mul_sub_neg then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.deriv_one_sub_mul_sub_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.deriv_one_sub_mul_sub_neg ``Submission.Real.smoothTransition.deriv_one_sub_mul_sub_neg

open _root_.Real _root_.Real.smoothTransition in
theorem deriv_one_sub_mul_sub_eq_neg_one {a b c t : ℝ} (hab : a < b) (ht : t < a) :
    deriv (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x)) t = -1 := by
  have hlocal : (fun x => (1 - Real.smoothTransition ((x - a) / (b - a))) * (c - x))
      =ᶠ[𝓝 t] (fun x => c - x) := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    exact one_sub_mul_sub_eq_sub hab hx.le
  rw [hlocal.deriv_eq]
  exact ((hasDerivAt_id t).const_sub c).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Real.smoothTransition.deriv_one_sub_mul_sub_eq_neg_one then
    throwError "Refusing to shadow existing declaration Real.smoothTransition.deriv_one_sub_mul_sub_eq_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Real.smoothTransition.deriv_one_sub_mul_sub_eq_neg_one ``Submission.Real.smoothTransition.deriv_one_sub_mul_sub_eq_neg_one

end Real.smoothTransition
