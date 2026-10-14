import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.Filter _root_.Set
open scoped _root_.Topology

variable {T : Type*} [MeasurableSpace T] {μ : Measure T} [IsFiniteMeasure μ]

open _root_.MeasureTheory in
theorem integrable_mul_and_abs_integral_le_of_ae_abs_le
    {f eta : T → ℝ} (hf : _root_.MeasureTheory.Integrable f μ) (heta : _root_.MeasureTheory.AEStronglyMeasurable eta μ)
    {C K : ℝ}
    (hfbound : ∀ᵐ t ∂μ, |f t| ≤ C) (hetabound : ∀ᵐ t ∂μ, |eta t| ≤ K) :
    _root_.MeasureTheory.Integrable (fun t => eta t * f t) μ ∧
      |∫ t, eta t * f t ∂μ| ≤ K * C * μ.real univ := by
  have hetaNorm : ∀ᵐ t ∂μ, ‖eta t‖ ≤ K := by
    simpa only [Real.norm_eq_abs] using hetabound
  have hnorm : ∀ᵐ t ∂μ, ‖eta t * f t‖ ≤ K * C := by
    filter_upwards [hfbound, hetabound] with t ht hetaT
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hetaT ht (abs_nonneg _) ((abs_nonneg _).trans hetaT)
  exact ⟨hf.bdd_mul heta hetaNorm,
    by simpa only [Real.norm_eq_abs] using _root_.MeasureTheory.norm_integral_le_of_norm_le_const hnorm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_mul_and_abs_integral_le_of_ae_abs_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_mul_and_abs_integral_le_of_ae_abs_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_mul_and_abs_integral_le_of_ae_abs_le ``Submission.MeasureTheory.integrable_mul_and_abs_integral_le_of_ae_abs_le

open _root_.MeasureTheory in
theorem tendsto_integral_mul_of_uniform_abs_bound_div
    {F : ℝ → T → ℝ} (hF : ∀ r : ℝ, 0 < r → _root_.MeasureTheory.Integrable (F r) μ)
    {C : ℝ} (hbound : ∀ r : ℝ, 0 < r → ∀ᵐ t ∂μ, |F r t| ≤ C / r)
    {eta : T → ℝ} (heta : _root_.MeasureTheory.AEStronglyMeasurable eta μ)
    {K : ℝ} (hetabound : ∀ᵐ t ∂μ, |eta t| ≤ K)
    {ι : Type*} {l : Filter ι} {R : ι → ℝ} (hR : _root_.Filter.Tendsto R l _root_.Filter.atTop) :
    Tendsto (fun i => ∫ t, eta t * F (R i) t ∂μ) l (𝓝 0) := by
  have hlarge : ∀ᶠ i in l, 0 < R i := hR.eventually (_root_.Filter.eventually_gt_atTop 0)
  have hb : ∀ᶠ i in l,
      ‖∫ t, eta t * F (R i) t ∂μ‖ ≤ K * (C / R i) * μ.real univ := by
    filter_upwards [hlarge] with i hi
    simpa only [Real.norm_eq_abs] using
      (integrable_mul_and_abs_integral_le_of_ae_abs_le
        (hF (R i) hi) heta (hbound (R i) hi) hetabound).2
  apply squeeze_zero_norm' hb
  have hz := ((hR.const_div_atTop C).const_mul K).mul_const (μ.real _root_.Set.univ)
  simpa only [_root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_mul_of_uniform_abs_bound_div then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_mul_of_uniform_abs_bound_div"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_mul_of_uniform_abs_bound_div ``Submission.MeasureTheory.tendsto_integral_mul_of_uniform_abs_bound_div

end MeasureTheory
