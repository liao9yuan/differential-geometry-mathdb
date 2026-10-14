import Mathlib.MeasureTheory.Function.L2Space

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Integration

noncomputable section

open _root_.MeasureTheory
open scoped _root_.ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem eLpNorm_two_sq_eq_lintegral_enorm_sq (f : α → ℝ) :
    (_root_.MeasureTheory.eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by rfl
  rw [h2]
  have h_integral : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine _root_.MeasureTheory.lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [h_integral, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.eLpNorm_two_sq_eq_lintegral_enorm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.eLpNorm_two_sq_eq_lintegral_enorm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.eLpNorm_two_sq_eq_lintegral_enorm_sq ``Submission.DifferentialGeometry.Analysis.Integration.eLpNorm_two_sq_eq_lintegral_enorm_sq

theorem integral_sq_eq_l2 {v : α → ℝ} (hv : _root_.MeasureTheory.MemLp v 2 μ) :
    (∫ x, v x ^ 2 ∂μ) = (_root_.MeasureTheory.eLpNorm v 2 μ).toReal ^ 2 := by
  have h_sq_lintegral :
      (_root_.MeasureTheory.eLpNorm v 2 μ) ^ 2 = ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    rw [_root_.MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by rfl
    rw [h2]
    have h_inner_eq : ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
        ∫⁻ x, (‖v x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
      refine _root_.MeasureTheory.lintegral_congr_ae ?_
      filter_upwards with x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have h_point : ∀ x : α,
      (‖v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (v x ^ 2) := by
    intro x
    rw [← Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [show v x ^ 2 = v x * v x by ring, enorm_mul]
    rw [show (‖v x‖ₑ : ℝ≥0∞) ^ 2 = ‖v x‖ₑ * ‖v x‖ₑ by ring]
  have h_sq_int : _root_.MeasureTheory.Integrable (fun x => v x ^ 2) μ := hv.integrable_sq
  have h_sq_nonneg : 0 ≤ᵐ[μ] fun x => v x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have h_sq :
      (_root_.MeasureTheory.eLpNorm v 2 μ) ^ 2 = ENNReal.ofReal (∫ x, v x ^ 2 ∂μ) := by
    rw [h_sq_lintegral, _root_.MeasureTheory.lintegral_congr fun x => h_point x]
    exact (_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_sq_int h_sq_nonneg).symm
  have h_int_nonneg : 0 ≤ ∫ x, v x ^ 2 ∂μ :=
    _root_.MeasureTheory.integral_nonneg fun x => sq_nonneg _
  have h_toReal :
      ((_root_.MeasureTheory.eLpNorm v 2 μ) ^ 2).toReal = (_root_.MeasureTheory.eLpNorm v 2 μ).toReal ^ 2 :=
    ENNReal.toReal_pow _ 2
  rw [h_sq, ENNReal.toReal_ofReal h_int_nonneg] at h_toReal
  exact h_toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 ``Submission.DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2

variable {F ι : Type*} [SeminormedAddCommGroup F]

theorem eLpNorm_two_le_of_integral_norm_sq_le {f : α → F} (hf : _root_.MeasureTheory.MemLp f 2 μ)
    {S : ℝ} (hS : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have hnorm : _root_.MeasureTheory.MemLp (fun x ↦ ‖f x‖) 2 μ :=
    hf.of_le_enorm hf.aestronglyMeasurable.norm
      (Filter.Eventually.of_forall fun x ↦ (enorm_norm (f x)).le)
  have heq : _root_.MeasureTheory.eLpNorm (fun x ↦ ‖f x‖) 2 μ = _root_.MeasureTheory.eLpNorm f 2 μ :=
    _root_.MeasureTheory.eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall fun x ↦ enorm_norm (f x))
  rw [← heq, hnorm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le ``Submission.DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_norm_sq_le

theorem eLpNorm_two_le_of_integral_sum_norm_sq_le
    {s : Finset ι} {f : ι → α → F} (hf : ∀ j ∈ s, _root_.MeasureTheory.MemLp (f j) 2 μ)
    {i : ι} (hi : i ∈ s) {S : ℝ}
    (hS : ∫ x, ∑ j ∈ s, ‖f j x‖ ^ 2 ∂μ ≤ S) :
    eLpNorm (f i) 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  apply eLpNorm_two_le_of_integral_norm_sq_le (hf i hi)
  have hnorm : ∀ j ∈ s, _root_.MeasureTheory.MemLp (fun x ↦ ‖f j x‖) 2 μ :=
    fun j hj ↦ (hf j hj).of_le_enorm (hf j hj).aestronglyMeasurable.norm
      (Filter.Eventually.of_forall fun x ↦ (enorm_norm (f j x)).le)
  have hsum : _root_.MeasureTheory.Integrable (fun x ↦ ∑ j ∈ s, ‖f j x‖ ^ 2) μ :=
    _root_.MeasureTheory.integrable_finsetSum s fun j hj ↦ (hnorm j hj).integrable_sq
  refine (_root_.MeasureTheory.integral_mono_ae (hnorm i hi).integrable_sq hsum ?_).trans hS
  exact Filter.Eventually.of_forall fun x ↦
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖f j x‖) hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_sum_norm_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_sum_norm_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_sum_norm_sq_le ``Submission.DifferentialGeometry.Analysis.Integration.eLpNorm_two_le_of_integral_sum_norm_sq_le

end

end DifferentialGeometry.Analysis.Integration
