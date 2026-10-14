import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def quadraticRadialCurve (b : ℝ) (x : E) (t : ℝ) : E :=
  Real.sqrt (1 + 2 * b * t / ‖x‖ ^ 2) • x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.quadraticRadialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve ``Submission.DifferentialGeometry.Analysis.ODE.quadraticRadialCurve

@[simp]
theorem quadraticRadialCurve_zero (b : ℝ) (x : E) : quadraticRadialCurve b x 0 = x := by
  simp [quadraticRadialCurve]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_zero ``Submission.DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_zero

theorem norm_sq_quadraticRadialCurve (b : ℝ) {x : E} (hx : x ≠ 0) {t : ℝ}
    (ht : 0 ≤ 1 + 2 * b * t / ‖x‖ ^ 2) :
    ‖quadraticRadialCurve b x t‖ ^ 2 = ‖x‖ ^ 2 + 2 * b * t := by
  rw [quadraticRadialCurve, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht]
  field_simp [norm_ne_zero_iff.mpr hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.norm_sq_quadraticRadialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.norm_sq_quadraticRadialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.norm_sq_quadraticRadialCurve ``Submission.DifferentialGeometry.Analysis.ODE.norm_sq_quadraticRadialCurve

theorem hasDerivAt_quadraticRadialCurve (b : ℝ) {x : E} (hx : x ≠ 0) {t : ℝ}
    (ht : 0 < 1 + 2 * b * t / ‖x‖ ^ 2) :
    HasDerivAt (quadraticRadialCurve b x)
      ((b / ‖quadraticRadialCurve b x t‖ ^ 2) • quadraticRadialCurve b x t) t := by
  have hinner : HasDerivAt (fun s : ℝ => 1 + 2 * b * s / ‖x‖ ^ 2) (2 * b / ‖x‖ ^ 2) t := by
    convert! (((hasDerivAt_id t).const_mul (2 * b)).div_const (‖x‖ ^ 2)).const_add 1 using 1
    simp
  have hs := (hinner.sqrt ht.ne').smul_const x
  convert! hs using 1
  rw [quadraticRadialCurve, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    smul_smul]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hx, (Real.sqrt_pos.mpr ht).ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.hasDerivAt_quadraticRadialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.hasDerivAt_quadraticRadialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.hasDerivAt_quadraticRadialCurve ``Submission.DifferentialGeometry.Analysis.ODE.hasDerivAt_quadraticRadialCurve

theorem isIntegralCurveOn_quadraticRadialCurve (b : ℝ) {x : E} (hx : x ≠ 0) :
    IsIntegralCurveOn (quadraticRadialCurve b x) (fun _ y => (b / ‖y‖ ^ 2) • y)
      {t | 0 < 1 + 2 * b * t / ‖x‖ ^ 2} :=
  fun _ ht => (hasDerivAt_quadraticRadialCurve b hx ht).hasDerivWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_quadraticRadialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_quadraticRadialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_quadraticRadialCurve ``Submission.DifferentialGeometry.Analysis.ODE.isIntegralCurveOn_quadraticRadialCurve

theorem quadraticRadialCurve_ne_zero (b : ℝ) {x : E} (hx : x ≠ 0) {t : ℝ}
    (ht : 0 < 1 + 2 * b * t / ‖x‖ ^ 2) : quadraticRadialCurve b x t ≠ 0 :=
  smul_ne_zero (Real.sqrt_pos.mpr ht).ne' hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_ne_zero ``Submission.DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_ne_zero

theorem quadraticRadialCurve_height {a : ℝ} (ha : a ≠ 0) (c : ℝ) {x : E} (hx : x ≠ 0)
    {t : ℝ} (ht : 0 ≤ 1 + 2 * (-a⁻¹) * t / ‖x‖ ^ 2) :
    c + a / 2 * ‖quadraticRadialCurve (-a⁻¹) x t‖ ^ 2 = c + a / 2 * ‖x‖ ^ 2 - t := by
  rw [norm_sq_quadraticRadialCurve _ hx ht]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_height ``Submission.DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_height

theorem continuousAt_quadraticRadialCurve (b : ℝ) {p : E × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt (fun q : E × ℝ => quadraticRadialCurve b q.1 q.2) p := by
  have hinner : ContinuousAt (fun q : E × ℝ => 1 + 2 * b * q.2 / ‖q.1‖ ^ 2) p :=
    continuousAt_const.add ((continuousAt_const.mul continuousAt_snd).div
      (continuousAt_fst.norm.pow 2) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hp)))
  exact (Real.continuous_sqrt.continuousAt.comp hinner).smul continuousAt_fst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.continuousAt_quadraticRadialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.continuousAt_quadraticRadialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.continuousAt_quadraticRadialCurve ``Submission.DifferentialGeometry.Analysis.ODE.continuousAt_quadraticRadialCurve

theorem contDiffOn_quadraticRadialCurve {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (b : ℝ) : ContDiffOn ℝ ∞ (fun p : ℝ × F => quadraticRadialCurve b p.2 p.1)
      {p | p.2 ≠ 0 ∧ 0 < 1 + 2 * b * p.1 / ‖p.2‖ ^ 2} := by
  intro p hp
  have hn : ‖p.2‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hp.1)
  have hinner : ContDiffAt ℝ ∞ (fun q : ℝ × F => 1 + 2 * b * q.1 / ‖q.2‖ ^ 2) p :=
    contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_fst).div (contDiffAt_snd.norm_sq ℝ) hn)
  exact ((hinner.sqrt hp.2.ne').smul contDiffAt_snd).contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.contDiffOn_quadraticRadialCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.contDiffOn_quadraticRadialCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.contDiffOn_quadraticRadialCurve ``Submission.DifferentialGeometry.Analysis.ODE.contDiffOn_quadraticRadialCurve

theorem quadraticRadialCurve_reverse_radicand
    {b t : ℝ} {x : E}
    (ht : 0 < 1 + 2 * b * t / ‖x‖ ^ 2) :
    1 + 2 * b * (-t) / ‖quadraticRadialCurve b x t‖ ^ 2 =
      (1 + 2 * b * t / ‖x‖ ^ 2)⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp only [quadraticRadialCurve, smul_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, div_zero, add_zero, inv_one]
  rw [norm_sq_quadraticRadialCurve b hx ht.le]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hr : ‖x‖ ^ 2 + 2 * b * t ≠ 0 := by
    have heq : ‖x‖ ^ 2 + 2 * b * t = ‖x‖ ^ 2 * (1 + 2 * b * t / ‖x‖ ^ 2) := by
      field_simp
    rw [heq]
    exact mul_ne_zero hn ht.ne'
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse_radicand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse_radicand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse_radicand ``Submission.DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse_radicand

theorem quadraticRadialCurve_reverse
    {b t : ℝ} {x : E}
    (ht : 0 < 1 + 2 * b * t / ‖x‖ ^ 2) :
    quadraticRadialCurve b (quadraticRadialCurve b x t) (-t) = x := by
  rw [quadraticRadialCurve, quadraticRadialCurve_reverse_radicand ht,
    quadraticRadialCurve, Real.sqrt_inv, smul_smul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr ht).ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse ``Submission.DifferentialGeometry.Analysis.ODE.quadraticRadialCurve_reverse

end DifferentialGeometry.Analysis.ODE
