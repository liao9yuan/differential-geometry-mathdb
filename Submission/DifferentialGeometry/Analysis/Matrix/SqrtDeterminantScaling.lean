import Submission.DifferentialGeometry.Tensor.LinearAlgebra.Matrix.ScalarInverse
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open _root_.Matrix in
theorem sqrt_det_sq_smul (G : Matrix ι ι ℝ) (r : ℝ) :
    Real.sqrt ((r ^ 2 • G).det) =
      |r| ^ Fintype.card ι * Real.sqrt G.det := by
  have hpow : (r ^ 2) ^ Fintype.card ι = (r ^ Fintype.card ι) ^ 2 := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [Matrix.det_smul, hpow, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, abs_pow]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.sqrt_det_sq_smul then
    throwError "Refusing to shadow existing declaration Matrix.sqrt_det_sq_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.sqrt_det_sq_smul ``Submission.Matrix.sqrt_det_sq_smul

open _root_.Matrix in
theorem sqrt_det_sq_smul_of_nonneg (G : Matrix ι ι ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt ((r ^ 2 • G).det) =
      r ^ Fintype.card ι * Real.sqrt G.det := by
  rw [sqrt_det_sq_smul, abs_of_nonneg hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.sqrt_det_sq_smul_of_nonneg then
    throwError "Refusing to shadow existing declaration Matrix.sqrt_det_sq_smul_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.sqrt_det_sq_smul_of_nonneg ``Submission.Matrix.sqrt_det_sq_smul_of_nonneg

open _root_.Matrix in
theorem sqrt_det_mul_inv_sq_smul (G : Matrix ι ι ℝ) (r : ℝ) (i j : ι) :
    Real.sqrt ((r ^ 2 • G).det) * ((r ^ 2 • G)⁻¹) i j =
      (|r| ^ Fintype.card ι / r ^ 2) * (Real.sqrt G.det * G⁻¹ i j) := by
  rw [sqrt_det_sq_smul, inv_smul_field]
  change (|r| ^ Fintype.card ι * Real.sqrt G.det) * ((r ^ 2)⁻¹ * G⁻¹ i j) = _
  simp only [div_eq_mul_inv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.sqrt_det_mul_inv_sq_smul then
    throwError "Refusing to shadow existing declaration Matrix.sqrt_det_mul_inv_sq_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.sqrt_det_mul_inv_sq_smul ``Submission.Matrix.sqrt_det_mul_inv_sq_smul

open _root_.Matrix in
theorem sqrt_det_mul_inv_sq_smul_of_nonneg (G : Matrix ι ι ℝ)
    {r : ℝ} (hr : 0 ≤ r) (i j : ι) :
    Real.sqrt ((r ^ 2 • G).det) * ((r ^ 2 • G)⁻¹) i j =
      (r ^ Fintype.card ι / r ^ 2) * (Real.sqrt G.det * G⁻¹ i j) := by
  rw [sqrt_det_mul_inv_sq_smul, abs_of_nonneg hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Matrix.sqrt_det_mul_inv_sq_smul_of_nonneg then
    throwError "Refusing to shadow existing declaration Matrix.sqrt_det_mul_inv_sq_smul_of_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `Matrix.sqrt_det_mul_inv_sq_smul_of_nonneg ``Submission.Matrix.sqrt_det_mul_inv_sq_smul_of_nonneg

end Matrix
