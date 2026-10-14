import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Filter
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {T M ι : Type*} [MeasurableSpace T] [MeasurableSpace M]
  {l : Filter ι} [l.IsCountablyGenerated]

open _root_.MeasureTheory in
theorem tendsto_integral_weighted_cutoff_mass
    (μ : _root_.MeasureTheory.Measure T) (ν : T → _root_.MeasureTheory.Measure M) (a : T → ℝ) (u : T → M → ℝ)
    (χ : ι → M → ℝ)
    (hχmeas : ∀ᶠ i in l, Measurable (χ i))
    (hχbound : ∀ᶠ i in l, ∀ x, ‖χ i x‖ ≤ 1)
    (hχone : ∀ x, _root_.Filter.Tendsto (fun i => χ i x) l (𝓝 1))
    (hu : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (u t) (ν t))
    (houter : ∀ᶠ i in l, _root_.MeasureTheory.AEStronglyMeasurable
      (fun t => a t * ∫ x, χ i x * u t x ∂ν t) μ)
    (hbound : _root_.MeasureTheory.Integrable (fun t => ‖a t‖ * ∫ x, ‖u t x‖ ∂ν t) μ) :
    _root_.Filter.Tendsto (fun i => ∫ t, a t * (∫ x, χ i x * u t x ∂ν t) ∂μ)
      l (𝓝 (∫ t, a t * (∫ x, u t x ∂ν t) ∂μ)) := by
  refine _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖a t‖ * ∫ x, ‖u t x‖ ∂ν t) houter ?_ hbound ?_
  · filter_upwards [hχbound] with i hi
    filter_upwards [hu] with t ht
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply _root_.MeasureTheory.norm_integral_le_of_norm_le ht.norm
    exact _root_.MeasureTheory.ae_of_all (ν t) fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hi x)
  · filter_upwards [hu] with t ht
    have hmass : _root_.Filter.Tendsto (fun i => ∫ x, χ i x * u t x ∂ν t)
        l (𝓝 (∫ x, u t x ∂ν t)) := by
      refine _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun x => ‖u t x‖) ?_ ?_ ht.norm ?_
      · exact hχmeas.mono fun i hi =>
          hi.aestronglyMeasurable.mul ht.aestronglyMeasurable
      · exact hχbound.mono fun i hi => _root_.MeasureTheory.ae_of_all (ν t) fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hi x)
      · exact _root_.MeasureTheory.ae_of_all (ν t) fun x => by
          simpa only [one_mul] using (hχone x).mul_const (u t x)
    exact tendsto_const_nhds.mul hmass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_weighted_cutoff_mass then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_weighted_cutoff_mass"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_weighted_cutoff_mass ``Submission.MeasureTheory.tendsto_integral_weighted_cutoff_mass

open _root_.MeasureTheory in
theorem tendsto_integral_weighted_cutoff_mass_zero_of_const_mass
    (μ : _root_.MeasureTheory.Measure T) (ν : T → _root_.MeasureTheory.Measure M) (a : T → ℝ) (u : T → M → ℝ)
    (χ : ι → M → ℝ)
    (hχmeas : ∀ᶠ i in l, Measurable (χ i))
    (hχbound : ∀ᶠ i in l, ∀ x, ‖χ i x‖ ≤ 1)
    (hχone : ∀ x, _root_.Filter.Tendsto (fun i => χ i x) l (𝓝 1))
    (hu : ∀ᵐ t ∂μ, _root_.MeasureTheory.Integrable (u t) (ν t))
    (hunonneg : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t, 0 ≤ u t x)
    (m : ℝ) (hmass : ∀ᵐ t ∂μ, (∫ x, u t x ∂ν t) = m)
    (ha : _root_.MeasureTheory.Integrable a μ) (hazero : (∫ t, a t ∂μ) = 0)
    (houter : ∀ᶠ i in l,
      _root_.MeasureTheory.AEStronglyMeasurable (fun t => ∫ x, χ i x * u t x ∂ν t) μ) :
    _root_.Filter.Tendsto (fun i => ∫ t, a t * (∫ x, χ i x * u t x ∂ν t) ∂μ)
      l (𝓝 0) := by
  have hnormmass : ∀ᵐ t ∂μ, (∫ x, ‖u t x‖ ∂ν t) = m := by
    filter_upwards [hunonneg, hmass] with t ht hmt
    rw [← hmt]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [ht] with x hx
    exact Real.norm_of_nonneg hx
  have hbound : _root_.MeasureTheory.Integrable (fun t => ‖a t‖ * ∫ x, ‖u t x‖ ∂ν t) μ := by
    apply (ha.norm.mul_const m).congr
    filter_upwards [hnormmass] with t ht
    rw [ht]
  have hlim := tendsto_integral_weighted_cutoff_mass μ ν a u χ hχmeas hχbound
    hχone hu (houter.mono fun _ hi => ha.aestronglyMeasurable.mul hi) hbound
  have hzero : (∫ t, a t * (∫ x, u t x ∂ν t) ∂μ) = 0 := by
    calc
      (∫ t, a t * (∫ x, u t x ∂ν t) ∂μ) = ∫ t, a t * m ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [hmass] with t ht
        rw [ht]
      _ = 0 := by rw [_root_.MeasureTheory.integral_mul_const, hazero, _root_.MulZeroClass.zero_mul]
  simpa only [hzero] using hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_weighted_cutoff_mass_zero_of_const_mass then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_weighted_cutoff_mass_zero_of_const_mass"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_weighted_cutoff_mass_zero_of_const_mass ``Submission.MeasureTheory.tendsto_integral_weighted_cutoff_mass_zero_of_const_mass

end MeasureTheory
