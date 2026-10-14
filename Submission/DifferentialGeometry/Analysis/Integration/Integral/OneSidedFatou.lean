import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.LiminfLimsup

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem integrable_of_tendsto_integral_of_eventually_le
    {A : Type*} [MeasurableSpace A] {μ : _root_.MeasureTheory.Measure A}
    {F : ℕ → A → ℝ} {f B : A → ℝ} {L : ℝ}
    (hF : ∀ n, _root_.MeasureTheory.Integrable (F n) μ) (hB : _root_.MeasureTheory.Integrable B μ)
    (hF_le : ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ x ∂μ, F n x ≤ B x)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => F n x) _root_.Filter.atTop (𝓝 (f x)))
    (hint : _root_.Filter.Tendsto (fun n => ∫ x, F n x ∂μ) _root_.Filter.atTop (𝓝 L)) :
    Integrable f μ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hF_le
  let G : ℕ → A → ℝ := fun n x => B x - F (n + N) x
  have hG : ∀ n, _root_.MeasureTheory.Integrable (G n) μ := fun n => hB.sub (hF (n + N))
  have hG_nonneg : ∀ n, ∀ᵐ x ∂μ, 0 ≤ G n x := fun n =>
    (hN (n + N) (Nat.le_add_left N n)).mono fun x hx => sub_nonneg.mpr hx
  have hGlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => G n x) _root_.Filter.atTop (𝓝 (B x - f x)) := by
    filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.sub (hx.comp (_root_.Filter.tendsto_add_atTop_nat N))
  have hGintegral : ∀ n, (∫⁻ x, ‖G n x‖ₑ ∂μ) =
      ENNReal.ofReal ((∫ x, B x ∂μ) - ∫ x, F (n + N) x ∂μ) := by
    intro n
    rw [← _root_.MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hG n)]
    congr 1
    calc
      (∫ x, ‖G n x‖ ∂μ) = ∫ x, G n x ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [hG_nonneg n] with x hx
        exact Real.norm_of_nonneg hx
      _ = _ := _root_.MeasureTheory.integral_sub hB (hF (n + N))
  have hGintlim : _root_.Filter.Tendsto (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) _root_.Filter.atTop
      (𝓝 (ENNReal.ofReal ((∫ x, B x ∂μ) - L))) := by
    simp_rw [hGintegral]
    exact ENNReal.tendsto_ofReal
      (tendsto_const_nhds.sub (hint.comp (_root_.Filter.tendsto_add_atTop_nat N)))
  have hGfin : _root_.MeasureTheory.Integrable (fun x => B x - f x) μ := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae _root_.Filter.atTop
      (fun n => (hG n).aestronglyMeasurable) hGlim, ?_⟩
    calc
      (∫⁻ x, ‖B x - f x‖ₑ ∂μ) = ∫⁻ x, _root_.Filter.liminf (fun n => ‖G n x‖ₑ) _root_.Filter.atTop ∂μ := by
        apply _root_.MeasureTheory.lintegral_congr_ae
        filter_upwards [hGlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ _root_.Filter.liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
        _root_.MeasureTheory.lintegral_liminf_le' (fun n => (hG n).aestronglyMeasurable.aemeasurable.enorm)
      _ < ⊤ := by rw [hGintlim.liminf_eq]; exact ENNReal.ofReal_lt_top
  have hfinal : _root_.MeasureTheory.Integrable (fun x => B x - (B x - f x)) μ := hB.sub hGfin
  simpa only [sub_sub_cancel] using hfinal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_of_tendsto_integral_of_eventually_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_of_tendsto_integral_of_eventually_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_of_tendsto_integral_of_eventually_le ``Submission.MeasureTheory.integrable_of_tendsto_integral_of_eventually_le

end MeasureTheory
