import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis

private theorem complex_eq_real_smul_add (z : ℂ) :
    z = z.re • (1 : ℂ) + z.im • Complex.I := by
  apply Complex.ext <;> simp [Complex.real_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.complex_eq_real_smul_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.complex_eq_real_smul_add target :: scope.openDecls } }

theorem bilinear_trace_unit_rotation
    (Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {e : ℂ} (he : ‖e‖ = 1) :
    Q e e + Q (Complex.I * e) (Complex.I * e) = Q 1 1 + Q Complex.I Complex.I := by
  have hnorm : e.re ^ 2 + e.im ^ 2 = 1 := by
    have h := Complex.sq_norm e
    rw [he] at h
    simpa only [Complex.normSq_apply, one_pow, pow_two, one_mul] using h.symm
  have heI : Complex.I * e = (-e.im) • (1 : ℂ) + e.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  calc
    _ = Q (e.re • 1 + e.im • Complex.I) (e.re • 1 + e.im • Complex.I) +
        Q ((-e.im) • 1 + e.re • Complex.I) ((-e.im) • 1 + e.re • Complex.I) := by
      rw [← heI, ← complex_eq_real_smul_add e]
    _ = _ := by
      simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
      linear_combination (Q 1 1 + Q Complex.I Complex.I) * hnorm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.bilinear_trace_unit_rotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.bilinear_trace_unit_rotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.bilinear_trace_unit_rotation ``Submission.DifferentialGeometry.Analysis.bilinear_trace_unit_rotation

theorem radial_inverse_quadratic_energy
    (Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (B : ℂ →L[ℝ] ℂ)
    {e e' : ℂ} (he' : ‖e'‖ = 1) {a : ℝ}
    (hr : B e' = e) (ht : B (Complex.I * e') = a⁻¹ • (Complex.I * e)) :
    a * (Q (B 1) (B 1) + Q (B Complex.I) (B Complex.I)) / 2 =
      (a * Q e e + a⁻¹ * Q (Complex.I * e) (Complex.I * e)) / 2 := by
  by_cases ha : a = 0
  · simp [ha]
  have hrot := bilinear_trace_unit_rotation (Q.bilinearComp B B) he'
  change Q (B e') (B e') + Q (B (Complex.I * e')) (B (Complex.I * e')) =
    Q (B 1) (B 1) + Q (B Complex.I) (B Complex.I) at hrot
  rw [← hrot, hr, ht]
  simp only [map_smul, _root_.smul_apply, smul_eq_mul]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.radial_inverse_quadratic_energy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.radial_inverse_quadratic_energy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.radial_inverse_quadratic_energy ``Submission.DifferentialGeometry.Analysis.radial_inverse_quadratic_energy

end DifferentialGeometry.Analysis

end

section

namespace DifferentialGeometry.Analysis

theorem bilinear_quadratic_sub_quarter_turn
    (Q : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (e : ℂ) :
    Q e e - Q (Complex.I * e) (Complex.I * e) =
      (e.re ^ 2 - e.im ^ 2) * Q 1 1 +
        (2 * e.re * e.im) * Q 1 Complex.I +
        (2 * e.re * e.im) * Q Complex.I 1 +
        (e.im ^ 2 - e.re ^ 2) * Q Complex.I Complex.I := by
  have hcoord (z : ℂ) : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  have hexpand (z : ℂ) :
      Q z z =
        z.re * (z.re * Q 1 1 + z.im * Q 1 Complex.I) +
          z.im * (z.re * Q Complex.I 1 + z.im * Q Complex.I Complex.I) := by
    calc
      Q z z = Q (z.re • (1 : ℂ) + z.im • Complex.I)
          (z.re • (1 : ℂ) + z.im • Complex.I) :=
        congrArg₂ (fun x y : ℂ => Q x y) (hcoord z) (hcoord z)
      _ = _ := by
        simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
  rw [hexpand e, hexpand (Complex.I * e), Complex.I_mul_re, Complex.I_mul_im]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.bilinear_quadratic_sub_quarter_turn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.bilinear_quadratic_sub_quarter_turn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.bilinear_quadratic_sub_quarter_turn ``Submission.DifferentialGeometry.Analysis.bilinear_quadratic_sub_quarter_turn

end DifferentialGeometry.Analysis

end
