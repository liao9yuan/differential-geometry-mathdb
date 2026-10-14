import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {α β E : Type*} [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tendsto_integral_zero_of_dominated_measure_family
    {l : Filter α} [l.IsCountablyGenerated]
    {μ : _root_.MeasureTheory.Measure β} {μs : α → _root_.MeasureTheory.Measure β} {F : α → β → E} {g : β → ℝ}
    (hμs : ∀ᶠ t in l, μs t ≤ μ)
    (hg : _root_.MeasureTheory.Integrable g μ)
    (hF_meas : ∀ᶠ t in l, _root_.MeasureTheory.AEStronglyMeasurable (F t) μ)
    (hF_bound : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖F t x‖ ≤ g x)
    (hF_limit : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun t => F t x) l (𝓝 0)) :
    Tendsto (fun t => ∫ x, F t x ∂μs t) l (𝓝 0) := by
  have hnorm_limit : _root_.Filter.Tendsto (fun t => ∫ x, ‖F t x‖ ∂μ) l (𝓝 0) := by
    have h := _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence g
      (hF_meas.mono fun t ht => ht.norm)
      (hF_bound.mono fun t ht => by simpa only [norm_norm] using ht) hg
      (hF_limit.mono fun x hx => by simpa only [norm_zero] using hx.norm)
    simpa only [_root_.MeasureTheory.integral_zero] using h
  apply squeeze_zero_norm' _ hnorm_limit
  filter_upwards [hμs, hF_meas, hF_bound] with t hμ hFm hFb
  calc
    ‖∫ x, F t x ∂μs t‖ ≤ ∫ x, ‖F t x‖ ∂μs t := _root_.MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖F t x‖ ∂μ := _root_.MeasureTheory.integral_mono_measure hμ
      (Eventually.of_forall fun x => norm_nonneg _) (hg.mono' hFm hFb).norm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_zero_of_dominated_measure_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_zero_of_dominated_measure_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_zero_of_dominated_measure_family ``Submission.DifferentialGeometry.Analysis.tendsto_integral_zero_of_dominated_measure_family

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ν : Measure α} {μ : Measure β} [IsFiniteMeasure ν]

theorem integrable_integral_of_dominated_measure_family
    {μs : α → _root_.MeasureTheory.Measure β} {F : α → β → E} {g : β → ℝ}
    {χ : ℕ → β → ℝ}
    (hμs : ∀ᵐ t ∂ν, μs t ≤ μ)
    (hg : _root_.MeasureTheory.Integrable g μ)
    (hF_meas : ∀ᵐ t ∂ν, _root_.MeasureTheory.AEStronglyMeasurable (F t) (μs t))
    (hF_bound : ∀ᵐ t ∂ν, ∀ᵐ x ∂μs t, ‖F t x‖ ≤ g x)
    (hχ_meas : ∀ᵐ t ∂ν, ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (χ n) (μs t))
    (hχ_bound : ∀ᵐ t ∂ν, ∀ n, ∀ᵐ x ∂μs t, ‖χ n x‖ ≤ 1)
    (hχ_limit : ∀ᵐ t ∂ν, ∀ᵐ x ∂μs t, _root_.Filter.Tendsto (fun n => χ n x) _root_.Filter.atTop (𝓝 1))
    (hcut_meas : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => ∫ x, χ n x • F t x ∂μs t) ν) :
    Integrable (fun t => ∫ x, F t x ∂μs t) ν := by
  have hF_int : ∀ᵐ t ∂ν, _root_.MeasureTheory.Integrable (F t) (μs t) := by
    filter_upwards [hμs, hF_meas, hF_bound] with t hμ hFm hFb
    exact (hg.mono_measure hμ).mono' hFm hFb
  have hlimit : ∀ᵐ t ∂ν, _root_.Filter.Tendsto
      (fun n => ∫ x, χ n x • F t x ∂μs t) _root_.Filter.atTop
      (𝓝 (∫ x, F t x ∂μs t)) := by
    filter_upwards [hF_int, hχ_meas, hχ_bound, hχ_limit] with t hFi hχm hχb hχl
    apply _root_.MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => ‖F t x‖)
    · intro n
      exact (hχm n).smul hFi.aestronglyMeasurable
    · exact hFi.norm
    · intro n
      filter_upwards [hχb n] with x hx
      rw [norm_smul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
    · filter_upwards [hχl] with x hx
      simpa only [one_smul] using hx.smul_const (F t x)
  have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (fun t => ∫ x, F t x ∂μs t) ν :=
    aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop hcut_meas hlimit
  refine (_root_.MeasureTheory.integrable_const (∫ x, ‖g x‖ ∂μ)).mono' hmeas ?_
  filter_upwards [hμs, hF_bound, hF_int] with t hμ hFb hFi
  calc
    ‖∫ x, F t x ∂μs t‖ ≤ ∫ x, ‖F t x‖ ∂μs t := _root_.MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x, g x ∂μs t := _root_.MeasureTheory.integral_mono_ae hFi.norm (hg.mono_measure hμ) hFb
    _ ≤ ∫ x, ‖g x‖ ∂μs t := _root_.MeasureTheory.integral_mono_ae (hg.mono_measure hμ)
      (hg.norm.mono_measure hμ) (Eventually.of_forall fun x => Real.le_norm_self _)
    _ ≤ ∫ x, ‖g x‖ ∂μ := _root_.MeasureTheory.integral_mono_measure hμ
      (Eventually.of_forall fun x => norm_nonneg _) hg.norm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_integral_of_dominated_measure_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_integral_of_dominated_measure_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_integral_of_dominated_measure_family ``Submission.DifferentialGeometry.Analysis.integrable_integral_of_dominated_measure_family

omit [MeasurableSpace α] [IsFiniteMeasure ν] in
theorem intervalIntegrable_integral_of_dominated_measure_family_on_Ioo
    {a b : ℝ} (hab : a ≤ b) {μ : _root_.MeasureTheory.Measure β}
    {μs : ℝ → _root_.MeasureTheory.Measure β} {F : ℝ → β → E} {g : β → ℝ}
    {χ : ℕ → β → ℝ}
    (hμs : ∀ t ∈ Set.Ioo a b, μs t ≤ μ)
    (hg : _root_.MeasureTheory.Integrable g μ)
    (hF_meas : ∀ t ∈ Set.Ioo a b, _root_.MeasureTheory.AEStronglyMeasurable (F t) (μs t))
    (hF_bound : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂μs t, ‖F t x‖ ≤ g x)
    (hχ_meas : ∀ t ∈ Set.Ioo a b, ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (χ n) (μs t))
    (hχ_bound : ∀ t ∈ Set.Ioo a b, ∀ n, ∀ᵐ x ∂μs t, ‖χ n x‖ ≤ 1)
    (hχ_limit : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂μs t,
      _root_.Filter.Tendsto (fun n => χ n x) _root_.Filter.atTop (𝓝 1))
    (hcut_cont : ∀ n, ContinuousOn
      (fun t => ∫ x, χ n x • F t x ∂μs t) (Set.Ioo a b)) :
    IntervalIntegrable (fun t => ∫ x, F t x ∂μs t) _root_.MeasureTheory.MeasureSpace.volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
  apply integrable_integral_of_dominated_measure_family
    (μ := μ) (χ := χ)
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hμs t ht
  · exact hg
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hF_meas t ht
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hF_bound t ht
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hχ_meas t ht
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hχ_bound t ht
  · filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hχ_limit t ht
  · intro n
    exact (hcut_cont n).aestronglyMeasurable measurableSet_Ioo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.intervalIntegrable_integral_of_dominated_measure_family_on_Ioo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.intervalIntegrable_integral_of_dominated_measure_family_on_Ioo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.intervalIntegrable_integral_of_dominated_measure_family_on_Ioo ``Submission.DifferentialGeometry.Analysis.intervalIntegrable_integral_of_dominated_measure_family_on_Ioo

end DifferentialGeometry.Analysis

end
