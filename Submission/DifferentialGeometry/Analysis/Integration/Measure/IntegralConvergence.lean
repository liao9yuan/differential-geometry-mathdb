import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem tendsto_integral_of_tendsto_lintegral_pos_neg
    {ι X : Type*} [MeasurableSpace X] {l : Filter ι}
    {μs : ι → _root_.MeasureTheory.Measure X} {μ : _root_.MeasureTheory.Measure X} {F : ι → X → ℝ} {f : X → ℝ}
    (hF : ∀ᶠ i in l, _root_.MeasureTheory.AEStronglyMeasurable (F i) (μs i))
    (hf : _root_.MeasureTheory.Integrable f μ)
    (hpos : _root_.Filter.Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (F i x) ∂μs i) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (f x) ∂μ)))
    (hneg : _root_.Filter.Tendsto (fun i => ∫⁻ x, ENNReal.ofReal (-F i x) ∂μs i) l
      (𝓝 (∫⁻ x, ENNReal.ofReal (-f x) ∂μ))) :
    Tendsto (fun i => ∫ x, F i x ∂μs i) l (𝓝 (∫ x, f x ∂μ)) := by
  have hpfin := hf.lintegral_lt_top.ne
  have hnfin := hf.neg.lintegral_lt_top.ne
  have hint : ∀ᶠ i in l, _root_.MeasureTheory.Integrable (F i) (μs i) := by
    filter_upwards [hF, hpos.eventually_ne hpfin, hneg.eventually_ne hnfin] with i hi hp hn
    have hpInt := _root_.MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp_aemeasurable hi.aemeasurable) hp
    have hnInt := _root_.MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp_aemeasurable hi.neg.aemeasurable) hn
    convert hpInt.sub hnInt using 1
    ext x
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, ENNReal.toReal_ofReal',
      max_zero_sub_max_neg_zero_eq_self]
  rw [_root_.MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  apply Tendsto.congr' (hint.mono fun i hi =>
    (_root_.MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm)
  exact ((ENNReal.tendsto_toReal hpfin).comp hpos).sub
    ((ENNReal.tendsto_toReal hnfin).comp hneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_of_tendsto_lintegral_pos_neg then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_of_tendsto_lintegral_pos_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_of_tendsto_lintegral_pos_neg ``Submission.MeasureTheory.tendsto_integral_of_tendsto_lintegral_pos_neg

end MeasureTheory
