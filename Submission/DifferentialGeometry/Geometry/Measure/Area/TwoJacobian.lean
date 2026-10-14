import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Continuous

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission












noncomputable section

open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]


def twoJacobian (v w : E) : ℝ :=
  Real.sqrt (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian ``Submission.DifferentialGeometry.Geometry.twoJacobian

theorem twoJacobian_eq_sqrt_det_gram (v w : E) :
    twoJacobian v w = Real.sqrt (Matrix.gram ℝ ![v, w]).det := by
  simp [twoJacobian, Matrix.det_fin_two, Matrix.gram, real_inner_comm w v, pow_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_eq_sqrt_det_gram then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_eq_sqrt_det_gram"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_eq_sqrt_det_gram ``Submission.DifferentialGeometry.Geometry.twoJacobian_eq_sqrt_det_gram

theorem twoJacobian_nonneg (v w : E) : 0 ≤ twoJacobian v w := Real.sqrt_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_nonneg ``Submission.DifferentialGeometry.Geometry.twoJacobian_nonneg

theorem twoJacobian_sq (v w : E) :
    twoJacobian v w ^ 2 = ⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2 := by
  apply Real.sq_sqrt
  have h := real_inner_mul_inner_self_le v w
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_sq ``Submission.DifferentialGeometry.Geometry.twoJacobian_sq

@[simp] theorem twoJacobian_zero_left (w : E) : twoJacobian 0 w = 0 := by
  simp [twoJacobian]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_zero_left ``Submission.DifferentialGeometry.Geometry.twoJacobian_zero_left

@[simp] theorem twoJacobian_zero_right (v : E) : twoJacobian v 0 = 0 := by
  simp [twoJacobian]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_zero_right ``Submission.DifferentialGeometry.Geometry.twoJacobian_zero_right

theorem twoJacobian_comm (v w : E) : twoJacobian v w = twoJacobian w v := by
  simp [twoJacobian, real_inner_comm w v, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_comm ``Submission.DifferentialGeometry.Geometry.twoJacobian_comm

theorem twoJacobian_le_norm_mul (v w : E) : twoJacobian v w ≤ ‖v‖ * ‖w‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ⟪v, w⟫_ℝ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_le_norm_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_le_norm_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_le_norm_mul ``Submission.DifferentialGeometry.Geometry.twoJacobian_le_norm_mul

theorem twoJacobian_of_orthogonal {v w : E} (h : ⟪v, w⟫_ℝ = 0) :
    twoJacobian v w = ‖v‖ * ‖w‖ := by
  rw [twoJacobian, h, zero_pow (by decide : 2 ≠ 0), sub_zero,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← mul_pow]
  exact Real.sqrt_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_of_orthogonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_of_orthogonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_of_orthogonal ``Submission.DifferentialGeometry.Geometry.twoJacobian_of_orthogonal


theorem twoJacobian_sub_smul (v w : E) (c : ℝ) :
    twoJacobian v (w - c • v) = twoJacobian v w := by
  unfold twoJacobian
  congr 1
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm w v]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_sub_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_sub_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_sub_smul ``Submission.DifferentialGeometry.Geometry.twoJacobian_sub_smul

@[simp] theorem twoJacobian_smul_self (v : E) (c : ℝ) : twoJacobian v (c • v) = 0 := by
  rw [← twoJacobian_sub_smul v (c • v) c, sub_self, twoJacobian_zero_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_smul_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_smul_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_smul_self ``Submission.DifferentialGeometry.Geometry.twoJacobian_smul_self


theorem twoJacobian_smul (v w : E) (c d : ℝ) :
    twoJacobian (c • v) (d • w) = |c * d| * twoJacobian v w := by
  unfold twoJacobian
  simp only [real_inner_smul_left, real_inner_smul_right]
  have h : (c * (c * ⟪v, v⟫_ℝ)) * (d * (d * ⟪w, w⟫_ℝ)) - (d * (c * ⟪v, w⟫_ℝ)) ^ 2 =
      (c * d) ^ 2 * (⟪v, v⟫_ℝ * ⟪w, w⟫_ℝ - ⟪v, w⟫_ℝ ^ 2) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_smul ``Submission.DifferentialGeometry.Geometry.twoJacobian_smul



theorem twoJacobian_le_of_norm_combinations_le {v w : E} {v' w' : F} {L : ℝ}
    (hL : 0 ≤ L) (h : ∀ a b : ℝ, ‖a • v' + b • w'‖ ≤ L * ‖a • v + b • w‖) :
    twoJacobian v' w' ≤ L ^ 2 * twoJacobian v w := by
  have hv : ‖v'‖ ≤ L * ‖v‖ := by simpa using h 1 0
  by_cases hv0 : v = 0
  · have hv' : v' = 0 := by simpa [hv0] using hv
    simp [hv0, hv']
  let c : ℝ := ⟪v, w⟫_ℝ / ⟪v, v⟫_ℝ
  have hden : ⟪v, v⟫_ℝ ≠ 0 := (real_inner_self_pos.mpr hv0).ne'
  have horth : ⟪v, w - c • v⟫_ℝ = 0 := by
    simp only [inner_sub_right, real_inner_smul_right, c]
    rw [div_mul_cancel₀ _ hden, sub_self]
  have hw : ‖w' - c • v'‖ ≤ L * ‖w - c • v‖ := by
    simpa [sub_eq_add_neg, add_comm] using h (-c) 1
  calc
    twoJacobian v' w' = twoJacobian v' (w' - c • v') := (twoJacobian_sub_smul _ _ _).symm
    _ ≤ ‖v'‖ * ‖w' - c • v'‖ := twoJacobian_le_norm_mul _ _
    _ ≤ (L * ‖v‖) * (L * ‖w - c • v‖) :=
      mul_le_mul hv hw (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))
    _ = L ^ 2 * (‖v‖ * ‖w - c • v‖) := by ring
    _ = L ^ 2 * twoJacobian v (w - c • v) := by rw [twoJacobian_of_orthogonal horth]
    _ = L ^ 2 * twoJacobian v w := by rw [twoJacobian_sub_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_le_of_norm_combinations_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_le_of_norm_combinations_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_le_of_norm_combinations_le ``Submission.DifferentialGeometry.Geometry.twoJacobian_le_of_norm_combinations_le


theorem twoJacobian_linearMap_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ₗ[ℝ] E) (B : V →ₗ[ℝ] F) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ x, ‖B x‖ ≤ L * ‖A x‖) (v w : V) :
    twoJacobian (B v) (B w) ≤ L ^ 2 * twoJacobian (A v) (A w) :=
  twoJacobian_le_of_norm_combinations_le hL (fun a b => by
    simpa only [map_add, map_smul] using h (a • v + b • w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.twoJacobian_linearMap_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.twoJacobian_linearMap_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.twoJacobian_linearMap_le ``Submission.DifferentialGeometry.Geometry.twoJacobian_linearMap_le

theorem continuous_twoJacobian : Continuous (fun p : E × E => twoJacobian p.1 p.2) := by
  unfold twoJacobian
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.continuous_twoJacobian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.continuous_twoJacobian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.continuous_twoJacobian ``Submission.DifferentialGeometry.Geometry.continuous_twoJacobian

end DifferentialGeometry.Geometry
