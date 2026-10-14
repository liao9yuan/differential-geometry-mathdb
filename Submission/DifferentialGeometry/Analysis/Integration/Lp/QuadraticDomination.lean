import Submission.DifferentialGeometry.Analysis.Integration.Lp.Bilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
theorem norm_integral_quadratic_le_integral_norm_sq
    (A : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ v w, _root_.MeasureTheory.AEStronglyMeasurable (fun x => A x v w) μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    {f : P → X} (hf : _root_.MeasureTheory.MemLp f 2 μ) :
    ‖∫ x, A x (f x) (f x) ∂μ‖ ≤ C * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hi := integrable_bilinear_of_apply_aestronglyMeasurable A hA hC hf hf
  have hs := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  calc
    _ ≤ ∫ x, ‖A x (f x) (f x)‖ ∂μ := _root_.MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖f x‖ ^ 2 ∂μ := by
      apply _root_.MeasureTheory.integral_mono_ae hi.norm (hs.const_mul C)
      filter_upwards [hC] with x hx
      calc
        ‖A x (f x) (f x)‖ ≤ ‖A x‖ * ‖f x‖ * ‖f x‖ := (A x).le_opNorm₂ _ _
        _ ≤ C * ‖f x‖ * ‖f x‖ := by gcongr
        _ = C * ‖f x‖ ^ 2 := by ring
    _ = _ := _root_.MeasureTheory.integral_const_mul _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.norm_integral_quadratic_le_integral_norm_sq then
    throwError "Refusing to shadow existing declaration MeasureTheory.norm_integral_quadratic_le_integral_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.norm_integral_quadratic_le_integral_norm_sq ``Submission.MeasureTheory.norm_integral_quadratic_le_integral_norm_sq

open _root_.MeasureTheory in
theorem norm_integral_quadratic_add_div_two_le
    (A : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ v w, _root_.MeasureTheory.AEStronglyMeasurable (fun x => A x v w) μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C)
    {a b : P → X} (ha : _root_.MeasureTheory.MemLp a 2 μ) (hb : _root_.MeasureTheory.MemLp b 2 μ) :
    ‖∫ x, (A x (a x) (a x) + A x (b x) (b x)) / 2 ∂μ‖ ≤
      C * ∫ x, (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 ∂μ := by
  have hia := integrable_bilinear_of_apply_aestronglyMeasurable A hA hC ha ha
  have hib := integrable_bilinear_of_apply_aestronglyMeasurable A hA hC hb hb
  have hsa := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha
  have hsb := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
  rw [_root_.MeasureTheory.integral_div, _root_.MeasureTheory.integral_add hia hib, norm_div,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), _root_.MeasureTheory.integral_div, _root_.MeasureTheory.integral_add hsa hsb]
  calc
    _ ≤ (‖∫ x, A x (a x) (a x) ∂μ‖ + ‖∫ x, A x (b x) (b x) ∂μ‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ((C * ∫ x, ‖a x‖ ^ 2 ∂μ) + C * ∫ x, ‖b x‖ ^ 2 ∂μ) / 2 := by
      gcongr
      · exact norm_integral_quadratic_le_integral_norm_sq A hA hC ha
      · exact norm_integral_quadratic_le_integral_norm_sq A hA hC hb
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.norm_integral_quadratic_add_div_two_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.norm_integral_quadratic_add_div_two_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.norm_integral_quadratic_add_div_two_le ``Submission.MeasureTheory.norm_integral_quadratic_add_div_two_le

open _root_.MeasureTheory in
theorem tendsto_integral_quadratic_add_div_two_of_tendsto_integral_norm_sq
    (μn : ℕ → _root_.MeasureTheory.Measure P) (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n v w, _root_.MeasureTheory.AEStronglyMeasurable (fun x => A n x v w) (μn n))
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μn n, ‖A n x‖ ≤ C)
    (a b : ℕ → P → X)
    (ha : ∀ n, _root_.MeasureTheory.MemLp (a n) 2 (μn n)) (hb : ∀ n, _root_.MeasureTheory.MemLp (b n) 2 (μn n))
    (hlim : _root_.Filter.Tendsto (fun n => ∫ x, (‖a n x‖ ^ 2 + ‖b n x‖ ^ 2) / 2 ∂μn n)
      _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto
      (fun n => ∫ x, (A n x (a n x) (a n x) + A n x (b n x) (b n x)) / 2 ∂μn n)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n =>
    norm_integral_quadratic_add_div_two_le (A n) (hA n) (hC n) (ha n) (hb n))
  simpa only [_root_.MulZeroClass.mul_zero] using hlim.const_mul C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_quadratic_add_div_two_of_tendsto_integral_norm_sq then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_quadratic_add_div_two_of_tendsto_integral_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_quadratic_add_div_two_of_tendsto_integral_norm_sq ``Submission.MeasureTheory.tendsto_integral_quadratic_add_div_two_of_tendsto_integral_norm_sq

end MeasureTheory
