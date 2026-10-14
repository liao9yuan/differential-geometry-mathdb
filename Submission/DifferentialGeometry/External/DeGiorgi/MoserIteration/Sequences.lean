-- Modified 2026-04-28: updated internal import paths for project namespace
import Submission.DifferentialGeometry.External.DeGiorgi.MoserIteration.Constants

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Moser Iteration Sequences

This module contains the geometric radii, exponent sequences, and the
basic algebraic lemmas that drive the Chapter 06 Moser iteration.
-/

noncomputable section

open _root_.MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

/-- The Sobolev gain factor `χ = d/(d-2)` in the elliptic Moser iteration. -/
noncomputable def moserChi (d : ℕ) [hNeZero : NeZero d] : ℝ := by
  let _ := hNeZero
  exact (d : ℝ) / ((d : ℝ) - 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserChi then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserChi"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserChi ``Submission.DeGiorgi.moserChi

/-- The standard nested radii `r_n = (1 + 2^{-n})/2`. -/
noncomputable def moserRadius (n : ℕ) : ℝ :=
  (1 + (1 / 2 : ℝ) ^ n) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserRadius then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserRadius ``Submission.DeGiorgi.moserRadius

/-- The exponent sequence `p_{n+1} = χ p_n`. -/
noncomputable def moserExponentSeq (d : ℕ) [NeZero d] (p₀ : ℝ) (n : ℕ) : ℝ :=
  p₀ * moserChi d ^ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserExponentSeq then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserExponentSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserExponentSeq ``Submission.DeGiorgi.moserExponentSeq

theorem moserDecayRatio_nonneg (hd : 2 < (d : ℝ)) :
    0 ≤ moserDecayRatio d := by
  have hd_nonneg : 0 ≤ ((d : ℝ) - 2) := by linarith
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  exact div_nonneg hd_nonneg hd_pos.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserDecayRatio_nonneg then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserDecayRatio_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserDecayRatio_nonneg ``Submission.DeGiorgi.moserDecayRatio_nonneg

theorem moserDecayRatio_lt_one (_hd : 2 < (d : ℝ)) :
    moserDecayRatio d < 1 := by
  let _ := _hd
  have hd_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  rw [moserDecayRatio]
  have : ((d : ℝ) - 2) < (d : ℝ) := by linarith
  exact (div_lt_one hd_pos).2 this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserDecayRatio_lt_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserDecayRatio_lt_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserDecayRatio_lt_one ``Submission.DeGiorgi.moserDecayRatio_lt_one

theorem moserChi_pos (hd : 2 < (d : ℝ)) :
    0 < moserChi d := by
  rw [moserChi]
  have hnum_pos : 0 < (d : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne d))
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  exact div_pos hnum_pos hden_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserChi_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserChi_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserChi_pos ``Submission.DeGiorgi.moserChi_pos

theorem one_lt_moserChi (hd : 2 < (d : ℝ)) :
    1 < moserChi d := by
  rw [moserChi]
  have hden_pos : 0 < (d : ℝ) - 2 := by linarith
  have : (d : ℝ) - 2 < (d : ℝ) := by linarith
  exact (one_lt_div hden_pos).2 this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.one_lt_moserChi then
    throwError "Refusing to shadow existing declaration DeGiorgi.one_lt_moserChi"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.one_lt_moserChi ``Submission.DeGiorgi.one_lt_moserChi

theorem one_le_moserChi (hd : 2 < (d : ℝ)) :
    1 ≤ moserChi d :=
  (one_lt_moserChi (d := d) hd).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.one_le_moserChi then
    throwError "Refusing to shadow existing declaration DeGiorgi.one_le_moserChi"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.one_le_moserChi ``Submission.DeGiorgi.one_le_moserChi

theorem moserRadius_zero :
    moserRadius 0 = 1 := by
  simp [moserRadius]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserRadius_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserRadius_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserRadius_zero ``Submission.DeGiorgi.moserRadius_zero

theorem moserRadius_le_one (n : ℕ) :
    moserRadius n ≤ 1 := by
  have hpow_le : (1 / 2 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  rw [moserRadius]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserRadius_le_one then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserRadius_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserRadius_le_one ``Submission.DeGiorgi.moserRadius_le_one

theorem moserRadius_pos (n : ℕ) :
    0 < moserRadius n := by
  rw [moserRadius]
  positivity

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserRadius_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserRadius_pos ``Submission.DeGiorgi.moserRadius_pos

theorem moserRadius_gap (n : ℕ) :
    moserRadius n - moserRadius (n + 1) = (1 / 2 : ℝ) ^ (n + 2) := by
  rw [moserRadius, moserRadius]
  rw [pow_succ]
  field_simp
  ring_nf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserRadius_gap then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserRadius_gap"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserRadius_gap ``Submission.DeGiorgi.moserRadius_gap

theorem moserRadius_succ_lt (n : ℕ) :
    moserRadius (n + 1) < moserRadius n := by
  have hgap : 0 < moserRadius n - moserRadius (n + 1) := by
    rw [moserRadius_gap]
    positivity
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserRadius_succ_lt then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserRadius_succ_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserRadius_succ_lt ``Submission.DeGiorgi.moserRadius_succ_lt

theorem moserExponentSeq_zero (p₀ : ℝ) :
    moserExponentSeq d p₀ 0 = p₀ := by
  simp [moserExponentSeq, moserChi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserExponentSeq_zero then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserExponentSeq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserExponentSeq_zero ``Submission.DeGiorgi.moserExponentSeq_zero

theorem moserExponentSeq_succ (p₀ : ℝ) (n : ℕ) :
    moserExponentSeq d p₀ (n + 1) = moserChi d * moserExponentSeq d p₀ n := by
  rw [moserExponentSeq, pow_succ, moserExponentSeq]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserExponentSeq_succ then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserExponentSeq_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserExponentSeq_succ ``Submission.DeGiorgi.moserExponentSeq_succ

theorem moserDecayRatio_eq_inv_moserChi (hd : 2 < (d : ℝ)) :
    moserDecayRatio d = (moserChi d)⁻¹ := by
  rw [moserDecayRatio, moserChi]
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne d)
  have hdm2_ne : (d : ℝ) - 2 ≠ 0 := by
    linarith
  field_simp [hd_ne, hdm2_ne]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserDecayRatio_eq_inv_moserChi then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserDecayRatio_eq_inv_moserChi"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserDecayRatio_eq_inv_moserChi ``Submission.DeGiorgi.moserDecayRatio_eq_inv_moserChi

theorem moserExponentSeq_pos (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 0 < p₀) (n : ℕ) :
    0 < moserExponentSeq d p₀ n := by
  rw [moserExponentSeq]
  exact mul_pos hp₀ (pow_pos (moserChi_pos (d := d) hd) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserExponentSeq_pos then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserExponentSeq_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserExponentSeq_pos ``Submission.DeGiorgi.moserExponentSeq_pos

theorem moserExponentSeq_ge_initial (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 0 ≤ p₀)
    (n : ℕ) :
    p₀ ≤ moserExponentSeq d p₀ n := by
  rw [moserExponentSeq]
  have hpow_ge : 1 ≤ moserChi d ^ n := by
    exact one_le_pow₀ (one_le_moserChi (d := d) hd)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.moserExponentSeq_ge_initial then
    throwError "Refusing to shadow existing declaration DeGiorgi.moserExponentSeq_ge_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.moserExponentSeq_ge_initial ``Submission.DeGiorgi.moserExponentSeq_ge_initial

theorem one_lt_moserExponentSeq (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 1 < p₀) (n : ℕ) :
    1 < moserExponentSeq d p₀ n := by
  have hp₀_nonneg : 0 ≤ p₀ := by linarith
  have hp_ge :
      p₀ ≤ moserExponentSeq d p₀ n :=
    moserExponentSeq_ge_initial (d := d) hd hp₀_nonneg n
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.one_lt_moserExponentSeq then
    throwError "Refusing to shadow existing declaration DeGiorgi.one_lt_moserExponentSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.one_lt_moserExponentSeq ``Submission.DeGiorgi.one_lt_moserExponentSeq

theorem inv_moserExponentSeq (hd : 2 < (d : ℝ)) {p₀ : ℝ} (hp₀ : 0 < p₀) (n : ℕ) :
    1 / moserExponentSeq d p₀ n = moserDecayRatio d ^ n / p₀ := by
  rw [moserExponentSeq]
  have hp₀_ne : p₀ ≠ 0 := hp₀.ne'
  have hchi_pos : 0 < moserChi d := moserChi_pos (d := d) hd
  have hchi_ne : moserChi d ≠ 0 := hchi_pos.ne'
  have hq_eq : moserDecayRatio d ^ n = (moserChi d ^ n)⁻¹ := by
    rw [moserDecayRatio_eq_inv_moserChi (d := d) hd, inv_pow]
  rw [hq_eq]
  field_simp [hp₀_ne, pow_ne_zero n hchi_ne]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.inv_moserExponentSeq then
    throwError "Refusing to shadow existing declaration DeGiorgi.inv_moserExponentSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.inv_moserExponentSeq ``Submission.DeGiorgi.inv_moserExponentSeq

end DeGiorgi
