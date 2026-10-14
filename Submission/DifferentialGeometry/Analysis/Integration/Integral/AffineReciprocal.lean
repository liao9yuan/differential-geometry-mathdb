import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory

namespace DifferentialGeometry.Analysis

theorem affine_reciprocal_taylor_remainder
    (A B t a : ℝ) (h : 1 + t * a ≠ 0) :
    ((1 + t * a) * A + (1 + t * a)⁻¹ * B) / 2 - (A + B) / 2 -
        t * a * (A - B) / 2 = t ^ 2 * a ^ 2 * B / (2 * (1 + t * a)) := by
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.affine_reciprocal_taylor_remainder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.affine_reciprocal_taylor_remainder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.affine_reciprocal_taylor_remainder ``Submission.DifferentialGeometry.Analysis.affine_reciprocal_taylor_remainder

theorem abs_affine_reciprocal_taylor_remainder_le
    (A B t a C : ℝ) (hB : 0 ≤ B) (ht : |t * a| ≤ 1 / 2) (ha : |a| ≤ C) :
    |((1 + t * a) * A + (1 + t * a)⁻¹ * B) / 2 - (A + B) / 2 -
        t * a * (A - B) / 2| ≤ C ^ 2 * t ^ 2 * B := by
  have hlow : 1 / 2 ≤ 1 + t * a := by linarith [(abs_le.mp ht).1]
  have hpos : 0 < 1 + t * a := by linarith
  have hsq : a ^ 2 ≤ C ^ 2 := sq_le_sq' (abs_le.mp ha).1 (abs_le.mp ha).2
  rw [affine_reciprocal_taylor_remainder A B t a (ne_of_gt hpos),
    abs_of_nonneg (by positivity)]
  calc
    t ^ 2 * a ^ 2 * B / (2 * (1 + t * a)) ≤ t ^ 2 * a ^ 2 * B :=
      div_le_self (by positivity) (by linarith)
    _ ≤ t ^ 2 * C ^ 2 * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (sq_nonneg t)) hB
    _ = C ^ 2 * t ^ 2 * B := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le ``Submission.DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le

theorem abs_affine_reciprocal_taylor_remainder_le_sum
    (A B t a C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : |t * a| ≤ 1 / 2) (ha : |a| ≤ C) :
    |((1 + t * a) * A + (1 + t * a)⁻¹ * B) / 2 - (A + B) / 2 -
        t * a * (A - B) / 2| ≤ C ^ 2 * t ^ 2 * (A + B) := by
  apply (abs_affine_reciprocal_taylor_remainder_le A B t a C hB ht ha).trans
  exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (sq_nonneg C) (sq_nonneg t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le_sum ``Submission.DifferentialGeometry.Analysis.abs_affine_reciprocal_taylor_remainder_le_sum

private theorem integrable_affine_reciprocal_sum
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} {A B a : α → ℝ}
    (hA : _root_.MeasureTheory.Integrable A μ) (hB : _root_.MeasureTheory.Integrable B μ) (ha : _root_.MeasureTheory.AEStronglyMeasurable a μ)
    {t : ℝ} (ht : ∀ᵐ x ∂μ, |t * a x| ≤ 1 / 2) :
    Integrable (fun x => ((1 + t * a x) * A x + (1 + t * a x)⁻¹ * B x) / 2) μ := by
  have hweight : _root_.MeasureTheory.AEStronglyMeasurable (fun x => 1 + t * a x) μ :=
    aestronglyMeasurable_const.add (ha.const_mul t)
  have hweight_bound : ∀ᵐ x ∂μ, ‖1 + t * a x‖ ≤ (3 : ℝ) / 2 := by
    filter_upwards [ht] with x hx
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hinvbound : ∀ᵐ x ∂μ, ‖(1 + t * a x)⁻¹‖ ≤ (2 : ℝ) := by
    filter_upwards [ht] with x hx
    have hpos : 0 < 1 + t * a x := by linarith [(abs_le.mp hx).1]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    linarith [(abs_le.mp hx).1]
  exact ((hA.bdd_mul hweight hweight_bound).add (hB.bdd_mul hweight.inv₀ hinvbound)).div_const 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrable_affine_reciprocal_sum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrable_affine_reciprocal_sum target :: scope.openDecls } }

theorem abs_integral_affine_reciprocal_taylor_remainder_le
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} {A B a : α → ℝ}
    (hA : _root_.MeasureTheory.Integrable A μ) (hB : _root_.MeasureTheory.Integrable B μ) (ha : _root_.MeasureTheory.AEStronglyMeasurable a μ)
    {t C : ℝ} (hBpos : ∀ᵐ x ∂μ, 0 ≤ B x)
    (ht : ∀ᵐ x ∂μ, |t * a x| ≤ 1 / 2) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) :
    |(∫ x, ((1 + t * a x) * A x + (1 + t * a x)⁻¹ * B x) / 2 ∂μ) -
        (∫ x, (A x + B x) / 2 ∂μ) - t * ∫ x, a x * (A x - B x) / 2 ∂μ| ≤
      C ^ 2 * t ^ 2 * ∫ x, B x ∂μ := by
  have hW := integrable_affine_reciprocal_sum hA hB ha ht
  have hE : _root_.MeasureTheory.Integrable (fun x => (A x + B x) / 2) μ := (hA.add hB).div_const 2
  have hR : _root_.MeasureTheory.Integrable (fun x => ((1 + t * a x) * A x +
      (1 + t * a x)⁻¹ * B x) / 2 - (A x + B x) / 2) μ := hW.sub hE
  have hS : _root_.MeasureTheory.Integrable (fun x => a x * (A x - B x) / 2) μ :=
    ((hA.sub hB).bdd_mul ha (by simpa only [Real.norm_eq_abs] using haC)).div_const 2
  calc
    _ = |∫ x, (((1 + t * a x) * A x + (1 + t * a x)⁻¹ * B x) / 2 -
        (A x + B x) / 2) - t * (a x * (A x - B x) / 2) ∂μ| := by
      rw [_root_.MeasureTheory.integral_sub hR (hS.const_mul t), _root_.MeasureTheory.integral_sub hW hE,
        _root_.MeasureTheory.integral_const_mul]
    _ ≤ ∫ x, C ^ 2 * t ^ 2 * B x ∂μ := by
      rw [← Real.norm_eq_abs]
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le (hB.const_mul (C ^ 2 * t ^ 2))
      filter_upwards [hBpos, ht, haC] with x hxB hxt hxa
      rw [Real.norm_eq_abs]
      have hrewrite : t * (a x * (A x - B x) / 2) =
          t * a x * (A x - B x) / 2 := by ring
      rw [hrewrite]
      exact abs_affine_reciprocal_taylor_remainder_le
        (A x) (B x) t (a x) C hxB hxt hxa
    _ = C ^ 2 * t ^ 2 * ∫ x, B x ∂μ := _root_.MeasureTheory.integral_const_mul _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le ``Submission.DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le

theorem abs_integral_affine_reciprocal_taylor_remainder_le_sum
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} {A B a : α → ℝ}
    (hA : _root_.MeasureTheory.Integrable A μ) (hB : _root_.MeasureTheory.Integrable B μ) (ha : _root_.MeasureTheory.AEStronglyMeasurable a μ)
    {t C : ℝ} (hApos : ∀ᵐ x ∂μ, 0 ≤ A x) (hBpos : ∀ᵐ x ∂μ, 0 ≤ B x)
    (ht : ∀ᵐ x ∂μ, |t * a x| ≤ 1 / 2) (haC : ∀ᵐ x ∂μ, |a x| ≤ C) :
    |(∫ x, ((1 + t * a x) * A x + (1 + t * a x)⁻¹ * B x) / 2 ∂μ) -
        (∫ x, (A x + B x) / 2 ∂μ) - t * ∫ x, a x * (A x - B x) / 2 ∂μ| ≤
      C ^ 2 * t ^ 2 * ∫ x, A x + B x ∂μ := by
  apply (abs_integral_affine_reciprocal_taylor_remainder_le hA hB ha hBpos ht haC).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg C) (sq_nonneg t))
  apply _root_.MeasureTheory.integral_mono_ae hB (hA.add hB)
  filter_upwards [hApos] with x hx
  change B x ≤ A x + B x
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le_sum ``Submission.DifferentialGeometry.Analysis.abs_integral_affine_reciprocal_taylor_remainder_le_sum

end DifferentialGeometry.Analysis
