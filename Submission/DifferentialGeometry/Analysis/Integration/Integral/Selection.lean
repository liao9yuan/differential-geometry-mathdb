import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter

open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

open _root_.MeasureTheory in
theorem exists_le_integral_sum_of_ae
    {f g : X → ℝ} (hf : _root_.MeasureTheory.Integrable f μ) (hg : _root_.MeasureTheory.Integrable g μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ f x ≤ (∫ y, f y ∂μ) + ∫ y, g y ∂μ ∧
      g x ≤ (∫ y, f y ∂μ) + ∫ y, g y ∂μ := by
  let N : Set X := {x | ¬ (P x ∧ 0 ≤ f x ∧ 0 ≤ g x)}
  have hN : μ N = 0 := by
    apply _root_.MeasureTheory.ae_iff.mp
    filter_upwards [hP, hf0, hg0] with x hx hf' hg'
    exact ⟨hx, hf', hg'⟩
  obtain ⟨x, hxN, hx⟩ := _root_.MeasureTheory.exists_notMem_null_le_integral (hf.add hg) hN
  have hp : P x ∧ 0 ≤ f x ∧ 0 ≤ g x := by simpa only [N, _root_.Set.mem_ofPred_eq, _root_.Classical.not_not] using hxN
  simp only [Pi.add_apply] at hx
  rw [_root_.MeasureTheory.integral_add hf hg] at hx
  exact ⟨x, hp.1, (le_add_of_nonneg_right hp.2.2).trans hx,
    (le_add_of_nonneg_left hp.2.1).trans hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_le_integral_sum_of_ae then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_le_integral_sum_of_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_le_integral_sum_of_ae ``Submission.MeasureTheory.exists_le_integral_sum_of_ae

open _root_.MeasureTheory in
theorem exists_energy_and_scaled_error_le_integral_sum
    {e d : X → ℝ} (he : _root_.MeasureTheory.Integrable e μ) (hd : _root_.MeasureTheory.Integrable d μ)
    (he0 : 0 ≤ᵐ[μ] e) (hd0 : 0 ≤ᵐ[μ] d) {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ x, P x ∧ e x ≤ (∫ y, e y ∂μ) + δ⁻¹ * ∫ y, d y ∂μ ∧
      d x ≤ δ * (∫ y, e y ∂μ) + ∫ y, d y ∂μ := by
  obtain ⟨x, hx, he', hd'⟩ := exists_le_integral_sum_of_ae he (hd.const_mul δ⁻¹) he0
    (hd0.mono fun x hx => mul_nonneg (inv_nonneg.mpr hδ.le) hx) hP
  rw [_root_.MeasureTheory.integral_const_mul] at he' hd'
  refine ⟨x, hx, he', ?_⟩
  have h := mul_le_mul_of_nonneg_left hd' hδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul] at h
  calc
    d x ≤ δ * ((∫ y, e y ∂μ) + δ⁻¹ * ∫ y, d y ∂μ) := h
    _ = _ := by rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_energy_and_scaled_error_le_integral_sum then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_energy_and_scaled_error_le_integral_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_energy_and_scaled_error_le_integral_sum ``Submission.MeasureTheory.exists_energy_and_scaled_error_le_integral_sum

open _root_.MeasureTheory in
theorem exists_tendsto_zero_and_eventually_le_of_scaled_integral
    {e d : ℕ → X → ℝ} (he : ∀ n, _root_.MeasureTheory.Integrable (e n) μ) (hd : ∀ n, _root_.MeasureTheory.Integrable (d n) μ)
    (he0 : ∀ n, 0 ≤ᵐ[μ] e n) (hd0 : ∀ n, 0 ≤ᵐ[μ] d n)
    {P : ℕ → X → Prop} (hP : ∀ n, ∀ᵐ x ∂μ, P n x)
    {B : ℝ} (hB : ∀ n, (∫ y, e n y ∂μ) ≤ B)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ0 : _root_.Filter.Tendsto δ _root_.Filter.atTop (𝓝 0))
    (hscaled : _root_.Filter.Tendsto (fun n => (δ n)⁻¹ * ∫ y, d n y ∂μ) _root_.Filter.atTop (𝓝 0)) :
    ∃ x : ℕ → X, (∀ n, P n (x n)) ∧
      _root_.Filter.Tendsto (fun n => d n (x n)) _root_.Filter.atTop (𝓝 0) ∧
      ∀ᶠ n in _root_.Filter.atTop, e n (x n) ≤ B + 1 := by
  classical
  have hselect (n : ℕ) := exists_energy_and_scaled_error_le_integral_sum (he n) (hd n)
    (he0 n) (hd0 n) ((hP n).and (hd0 n)) (hδ n)
  choose x hx hxe hxd using hselect
  refine ⟨x, fun n => (hx n).1, ?_, ?_⟩
  · have hD : _root_.Filter.Tendsto (fun n => ∫ y, d n y ∂μ) _root_.Filter.atTop (𝓝 0) := by
      have h := hδ0.mul hscaled
      simpa only [← mul_assoc, mul_inv_cancel₀ (hδ _).ne', one_mul, _root_.MulZeroClass.mul_zero] using h
    have hupper : _root_.Filter.Tendsto (fun n => δ n * B + ∫ y, d n y ∂μ) _root_.Filter.atTop (𝓝 0) := by
      simpa only [_root_.MulZeroClass.zero_mul, zero_add] using (hδ0.mul_const B).add hD
    exact squeeze_zero (fun n => (hx n).2)
      (fun n => (hxd n).trans (add_le_add (mul_le_mul_of_nonneg_left (hB n)
        (hδ n).le) le_rfl)) hupper
  · filter_upwards [hscaled.eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with n hn
    exact (hxe n).trans (add_le_add (hB n) hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_tendsto_zero_and_eventually_le_of_scaled_integral then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_tendsto_zero_and_eventually_le_of_scaled_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_tendsto_zero_and_eventually_le_of_scaled_integral ``Submission.MeasureTheory.exists_tendsto_zero_and_eventually_le_of_scaled_integral

open _root_.MeasureTheory in
theorem exists_tendsto_zero_and_eventually_le_of_integral
    {e d : ℕ → X → ℝ} (he : ∀ n, _root_.MeasureTheory.Integrable (e n) μ) (hd : ∀ n, _root_.MeasureTheory.Integrable (d n) μ)
    (he0 : ∀ n, 0 ≤ᵐ[μ] e n) (hd0 : ∀ n, 0 ≤ᵐ[μ] d n)
    {P : ℕ → X → Prop} (hP : ∀ n, ∀ᵐ x ∂μ, P n x)
    {B : ℝ} (hB : ∀ n, (∫ y, e n y ∂μ) ≤ B)
    (hD : _root_.Filter.Tendsto (fun n => ∫ y, d n y ∂μ) _root_.Filter.atTop (𝓝 0)) :
    ∃ x : ℕ → X, (∀ n, P n (x n)) ∧
      _root_.Filter.Tendsto (fun n => d n (x n)) _root_.Filter.atTop (𝓝 0) ∧
      ∀ᶠ n in _root_.Filter.atTop, e n (x n) ≤ B + 1 := by
  let δ : ℕ → ℝ := fun n => Real.sqrt (∫ y, d n y ∂μ) + 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by
    exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by positivity)
  have hδ0 : _root_.Filter.Tendsto δ _root_.Filter.atTop (𝓝 0) := by
    simpa only [δ, Real.sqrt_zero, zero_add] using
      hD.sqrt.add (tendsto_one_div_add_atTop_nhds_zero_nat :
        _root_.Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) _root_.Filter.atTop (𝓝 0))
  apply exists_tendsto_zero_and_eventually_le_of_scaled_integral he hd he0 hd0 hP hB hδ hδ0
  have hn (n : ℕ) : 0 ≤ ∫ y, d n y ∂μ := _root_.MeasureTheory.integral_nonneg_of_ae (hd0 n)
  apply squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (hδ n).le) (hn n))
    (fun n => ?_) (by simpa only [Real.sqrt_zero] using hD.sqrt)
  rw [inv_mul_le_iff₀ (hδ n)]
  dsimp [δ]
  rw [add_mul, Real.mul_self_sqrt (hn n)]
  exact le_add_of_nonneg_right (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_tendsto_zero_and_eventually_le_of_integral then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_tendsto_zero_and_eventually_le_of_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_tendsto_zero_and_eventually_le_of_integral ``Submission.MeasureTheory.exists_tendsto_zero_and_eventually_le_of_integral

end MeasureTheory

end

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter

open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

open _root_.MeasureTheory in
theorem exists_tendsto_zero_and_eventually_le_of_finite_integral
    [_root_.MeasureTheory.IsFiniteMeasure μ] [NeZero μ]
    {e d : ℕ → X → ℝ} (he : ∀ n, _root_.MeasureTheory.Integrable (e n) μ) (hd : ∀ n, _root_.MeasureTheory.Integrable (d n) μ)
    (he0 : ∀ n, 0 ≤ᵐ[μ] e n) (hd0 : ∀ n, 0 ≤ᵐ[μ] d n)
    {P : ℕ → X → Prop} (hP : ∀ n, ∀ᵐ x ∂μ, P n x)
    {B : ℝ} (hB : ∀ n, (∫ y, e n y ∂μ) ≤ B)
    (hD : _root_.Filter.Tendsto (fun n => ∫ y, d n y ∂μ) _root_.Filter.atTop (𝓝 0)) :
    ∃ x : ℕ → X, (∀ n, P n (x n)) ∧
      _root_.Filter.Tendsto (fun n => d n (x n)) _root_.Filter.atTop (𝓝 0) ∧
      ∀ᶠ n in _root_.Filter.atTop, e n (x n) ≤ (μ.real _root_.Set.univ)⁻¹ * B + 1 := by
  let ν : _root_.MeasureTheory.Measure X := (μ _root_.Set.univ)⁻¹ • μ
  have hE (n : ℕ) : (∫ y, e n y ∂ν) ≤ (μ.real _root_.Set.univ)⁻¹ * B := by
    change (⨍ y, e n y ∂μ) ≤ _
    rw [_root_.MeasureTheory.average_eq, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hB n) (inv_nonneg.mpr (_root_.MeasureTheory.measureReal_nonneg))
  have hD' : _root_.Filter.Tendsto (fun n => ∫ y, d n y ∂ν) _root_.Filter.atTop (𝓝 0) := by
    change _root_.Filter.Tendsto (fun n => ⨍ y, d n y ∂μ) _root_.Filter.atTop (𝓝 0)
    simp_rw [_root_.MeasureTheory.average_eq, smul_eq_mul]
    simpa only [_root_.MulZeroClass.mul_zero] using hD.const_mul (μ.real _root_.Set.univ)⁻¹
  exact exists_tendsto_zero_and_eventually_le_of_integral
    (fun n => (he n).to_average) (fun n => (hd n).to_average)
    (fun n => Measure.ae_smul_measure (he0 n) _) (fun n => Measure.ae_smul_measure (hd0 n) _)
    (fun n => Measure.ae_smul_measure (hP n) _) hE hD'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_tendsto_zero_and_eventually_le_of_finite_integral then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_tendsto_zero_and_eventually_le_of_finite_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_tendsto_zero_and_eventually_le_of_finite_integral ``Submission.MeasureTheory.exists_tendsto_zero_and_eventually_le_of_finite_integral

end MeasureTheory

end
