import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Filter
open scoped _root_.Topology _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem tendsto_lintegral_of_dominated_convergence_of_measure_sandwich
    {X ι : Type*} [MeasurableSpace X] {l : Filter ι} [l.IsCountablyGenerated]
    {μ : _root_.MeasureTheory.Measure X} {ν : ι → _root_.MeasureTheory.Measure X} {c : ι → ℝ≥0∞}
    {F : ι → X → ℝ≥0∞} {f : X → ℝ≥0∞} (bound : X → ℝ≥0∞)
    (hmeas : ∀ᶠ i in l, Measurable (F i))
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, F i x ≤ bound x)
    (hfin : ∫⁻ x, bound x ∂μ ≠ ∞)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun i => F i x) l (𝓝 (f x)))
    (hc : _root_.Filter.Tendsto c l (𝓝 1))
    (hlower : ∀ᶠ i in l, μ ≤ ν i)
    (hupper : ∀ᶠ i in l, ν i ≤ c i • μ) :
    Tendsto (fun i => ∫⁻ x, F i x ∂ν i) l (𝓝 (∫⁻ x, f x ∂μ)) := by
  have hfixed := _root_.MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence bound hmeas hbound hfin hlim
  have hright : _root_.Filter.Tendsto (fun i => c i * ∫⁻ x, F i x ∂μ) l (𝓝 (∫⁻ x, f x ∂μ)) := by
    simpa only [one_mul] using
      ENNReal.Tendsto.mul hc (Or.inl one_ne_zero) hfixed (Or.inr ENNReal.one_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hfixed hright
  · filter_upwards [hlower] with i hi
    exact _root_.MeasureTheory.lintegral_mono' hi (fun _ => le_rfl)
  · filter_upwards [hupper] with i hi
    simpa only [_root_.MeasureTheory.lintegral_smul_measure, smul_eq_mul] using
      (_root_.MeasureTheory.lintegral_mono' hi (fun x => le_rfl : ∀ x, F i x ≤ F i x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_lintegral_of_dominated_convergence_of_measure_sandwich then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_lintegral_of_dominated_convergence_of_measure_sandwich"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_lintegral_of_dominated_convergence_of_measure_sandwich ``Submission.MeasureTheory.tendsto_lintegral_of_dominated_convergence_of_measure_sandwich

end MeasureTheory
