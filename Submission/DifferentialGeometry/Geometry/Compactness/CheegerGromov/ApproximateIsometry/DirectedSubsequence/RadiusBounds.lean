import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

section DirectedRadii

def openRadius (j l : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.openRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.openRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.openRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.openRadius

theorem two_pow_lt_openRadius (j l : ℕ) :
    (2 : ℝ) ^ j < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  dsimp [openRadius]
  calc
    (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
    _ < (2 : ℝ) ^ j * (1 + (1 / 2 : ℝ) ^ (l + 1)) :=
      mul_lt_mul_of_pos_left (by linarith) hpow

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.two_pow_lt_openRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.two_pow_lt_openRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.two_pow_lt_openRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.two_pow_lt_openRadius

theorem openRadius_pos (j l : ℕ) :
    0 < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  dsimp [openRadius]
  nlinarith [mul_pos hpow (by linarith : (0 : ℝ) < 1 + (1 / 2 : ℝ) ^ (l + 1))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.openRadius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.openRadius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.openRadius_pos ``Submission.DifferentialGeometry.CheegerGromovCompactness.openRadius_pos

theorem openRadius_succ_lt (j l : ℕ) :
    openRadius j (l + 1) < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [openRadius]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt ``Submission.DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt

def midRadius (j l : ℕ) : ℝ :=
  (2 : ℝ) ^ j * (1 + (((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.midRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.midRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.midRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.midRadius

theorem openRadius_succ_lt_midRadius (j l : ℕ) :
    openRadius j (l + 1) < midRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [openRadius, midRadius]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt_midRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt_midRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt_midRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.openRadius_succ_lt_midRadius

theorem midRadius_lt_openRadius (j l : ℕ) :
    midRadius j l < openRadius j l := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail : 0 < (1 / 2 : ℝ) ^ (l + 1) := by positivity
  have hsplit : (1 / 2 : ℝ) ^ (l + 2) = (1 / 2 : ℝ) ^ (l + 1) * (1 / 2) := by
    rw [show l + 2 = l + 1 + 1 by omega, pow_succ]
  dsimp [openRadius, midRadius]
  refine mul_lt_mul_of_pos_left ?_ hpow
  rw [hsplit]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.midRadius_lt_openRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.midRadius_lt_openRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.midRadius_lt_openRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.midRadius_lt_openRadius

theorem midRadius_le_two_pow_succ (j l : ℕ) :
    midRadius j l ≤ (2 : ℝ) ^ (j + 1) := by
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  calc
    midRadius j l = (2 : ℝ) ^ j *
        (1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2) := by
      rfl
    _ ≤ (2 : ℝ) ^ j * (1 + (1 + 1) / 2) := by
      have hinner :
          1 + ((1 / 2 : ℝ) ^ (l + 1) + (1 / 2 : ℝ) ^ (l + 2)) / 2
            ≤ 1 + (1 + 1) / 2 := by
        linarith
      exact mul_le_mul_of_nonneg_left hinner hpow.le
    _ = (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ']
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.midRadius_le_two_pow_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.midRadius_le_two_pow_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.midRadius_le_two_pow_succ ``Submission.DifferentialGeometry.CheegerGromovCompactness.midRadius_le_two_pow_succ

theorem midRadius_le_zero (j l : ℕ) :
    midRadius j l ≤ midRadius j 0 := by
  have hpow : 0 ≤ (2 : ℝ) ^ j := by positivity
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  dsimp [midRadius]
  refine mul_le_mul_of_nonneg_left ?_ hpow
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.midRadius_le_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.midRadius_le_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.midRadius_le_zero ``Submission.DifferentialGeometry.CheegerGromovCompactness.midRadius_le_zero

theorem half_pow_succ_le_half (j : ℕ) :
    (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
  have hpow : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  simpa using hpow

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.half_pow_succ_le_half then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.half_pow_succ_le_half"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.half_pow_succ_le_half ``Submission.DifferentialGeometry.CheegerGromovCompactness.half_pow_succ_le_half

theorem sqrt_one_add_mul_openRadius_succ_lt_two_pow {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * openRadius j (l + 1) < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 3 / 2 := by
    have hlt : 1 + a < (3 / 2 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((3 / 2 : ℝ) ^ 2) = 3 / 2 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail_le : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hpow_pos : 0 < (2 : ℝ) ^ j := by positivity
  have hR_pos : 0 < openRadius j (l + 1) := openRadius_pos j (l + 1)
  have hR_le :
      openRadius j (l + 1) ≤ (5 / 4 : ℝ) * (2 : ℝ) ^ j := by
    dsimp [openRadius]
    nlinarith
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * openRadius j (l + 1)
        < (3 / 2 : ℝ) * openRadius j (l + 1) :=
          mul_lt_mul_of_pos_right hsqrt_lt hR_pos
    _ ≤ (3 / 2 : ℝ) * ((5 / 4 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hR_le (by norm_num)
    _ = (15 / 8 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_openRadius_succ_lt_two_pow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_openRadius_succ_lt_two_pow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_openRadius_succ_lt_two_pow ``Submission.DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_openRadius_succ_lt_two_pow

theorem sqrt_one_add_mul_midRadius_lt_two_pow {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRadius j l < (2 : ℝ) ^ (j + l + 1) := by
  have harg_nonneg : 0 ≤ 1 + a := by linarith
  have hsqrt_lt : Real.sqrt (1 + a) < 5 / 4 := by
    have hlt : 1 + a < (5 / 4 : ℝ) ^ 2 := by nlinarith
    have hs := Real.sqrt_lt_sqrt harg_nonneg hlt
    have hsqrt_sq : Real.sqrt ((5 / 4 : ℝ) ^ 2) = 5 / 4 := by
      rw [Real.sqrt_sq]
      norm_num
    simpa [hsqrt_sq] using hs
  have htail₁ : (1 / 2 : ℝ) ^ (l + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have htail₂ : (1 / 2 : ℝ) ^ (l + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmid_pos : 0 < midRadius j l := by
    dsimp [midRadius]
    positivity
  have hmid_le : midRadius j l ≤ (11 / 8 : ℝ) * (2 : ℝ) ^ j := by
    dsimp [midRadius]
    nlinarith [show 0 ≤ (2 : ℝ) ^ j by positivity]
  have hpow_mono : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (j + l + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  calc
    Real.sqrt (1 + a) * midRadius j l
        < (5 / 4 : ℝ) * midRadius j l := mul_lt_mul_of_pos_right hsqrt_lt hmid_pos
    _ ≤ (5 / 4 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hmid_le (by norm_num)
    _ = (55 / 32 : ℝ) * (2 : ℝ) ^ j := by ring
    _ < 2 * (2 : ℝ) ^ j := by nlinarith [show 0 < (2 : ℝ) ^ j by positivity]
    _ = (2 : ℝ) ^ (j + 1) := by rw [pow_succ']
    _ ≤ (2 : ℝ) ^ (j + l + 1) := hpow_mono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_two_pow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_two_pow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_two_pow ``Submission.DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_two_pow

theorem sqrt_one_add_mul_midRadius_lt_next_openRadius {a : ℝ} (j l : ℕ) (ha0 : 0 < a) (ha2 : a ≤ 1 / 2) :
    Real.sqrt (1 + a) * midRadius j l < openRadius (j + 1) l := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + a) := Real.sqrt_nonneg _
  have hle_mid0 : Real.sqrt (1 + a) * midRadius j l ≤ Real.sqrt (1 + a) * midRadius j 0 :=
    mul_le_mul_of_nonneg_left (midRadius_le_zero j l) hsqrt_nonneg
  have hlt_step : Real.sqrt (1 + a) * midRadius j 0 < (2 : ℝ) ^ (j + 1) := by
    simpa using sqrt_one_add_mul_midRadius_lt_two_pow j 0 ha0 ha2
  exact lt_trans (lt_of_le_of_lt hle_mid0 hlt_step) (two_pow_lt_openRadius (j + 1) l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_next_openRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_next_openRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_next_openRadius ``Submission.DifferentialGeometry.CheegerGromovCompactness.sqrt_one_add_mul_midRadius_lt_next_openRadius

end DirectedRadii

end CheegerGromovCompactness
end DifferentialGeometry
