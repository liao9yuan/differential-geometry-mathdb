import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem integrable_prod_and_integral_le_of_fiber_integral_le
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : _root_.MeasureTheory.Measure T} {μ : _root_.MeasureTheory.Measure X} [_root_.MeasureTheory.SFinite ν] [_root_.MeasureTheory.SFinite μ]
    {F G H : T × X → ℝ} (hFmeas : _root_.MeasureTheory.AEStronglyMeasurable F (ν.prod μ))
    (hG : _root_.MeasureTheory.Integrable G (ν.prod μ)) (hH : _root_.MeasureTheory.Integrable H (ν.prod μ))
    (hF : ∀ᵐ t ∂ν, _root_.MeasureTheory.Integrable (fun x => F (t, x)) μ)
    (hFG : ∀ᵐ p ∂ν.prod μ, F p ≤ G p)
    (hHF : ∀ᵐ t ∂ν, (∫ x, H (t, x) ∂μ) ≤ ∫ x, F (t, x) ∂μ) :
    Integrable F (ν.prod μ) ∧ (∫ p, H p ∂ν.prod μ) ≤ ∫ p, F p ∂ν.prod μ := by
  have hmajor : _root_.MeasureTheory.Integrable
      (fun t => 2 * (∫ x, ‖G (t, x)‖ ∂μ) - ∫ x, H (t, x) ∂μ) ν :=
    (hG.integral_norm_prod_left.const_mul 2).sub hH.integral_prod_left
  have hnorm : _root_.MeasureTheory.Integrable (fun t => ∫ x, ‖F (t, x)‖ ∂μ) ν := by
    apply hmajor.mono' hFmeas.norm.integral_prod_right'
    filter_upwards [hF, hG.prod_right_ae, Measure.ae_ae_of_ae_prod hFG, hHF] with t ht htG htFG htHF
    rw [Real.norm_of_nonneg (_root_.MeasureTheory.integral_nonneg fun x => norm_nonneg (F (t, x)))]
    have hbound : (∫ x, ‖F (t, x)‖ ∂μ) ≤
        ∫ x, 2 * ‖G (t, x)‖ - F (t, x) ∂μ := by
      apply _root_.MeasureTheory.integral_mono_ae ht.norm ((htG.norm.const_mul 2).sub ht)
      filter_upwards [htFG] with x hx
      change ‖F (t, x)‖ ≤ 2 * ‖G (t, x)‖ - F (t, x)
      have hGnorm : G (t, x) ≤ ‖G (t, x)‖ := le_abs_self _
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · linarith [norm_nonneg (G (t, x))]
      · linarith
    rw [_root_.MeasureTheory.integral_sub (htG.norm.const_mul 2) ht, _root_.MeasureTheory.integral_const_mul] at hbound
    linarith
  have hFprod : _root_.MeasureTheory.Integrable F (ν.prod μ) := (_root_.MeasureTheory.integrable_prod_iff hFmeas).mpr ⟨hF, hnorm⟩
  refine ⟨hFprod, ?_⟩
  rw [_root_.MeasureTheory.integral_prod H hH, _root_.MeasureTheory.integral_prod F hFprod]
  exact _root_.MeasureTheory.integral_mono_ae hH.integral_prod_left hFprod.integral_prod_left hHF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_prod_and_integral_le_of_fiber_integral_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_prod_and_integral_le_of_fiber_integral_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_prod_and_integral_le_of_fiber_integral_le ``Submission.MeasureTheory.integrable_prod_and_integral_le_of_fiber_integral_le

end MeasureTheory
