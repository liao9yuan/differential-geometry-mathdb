import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.MeasureTheory in
theorem tendsto_integral_of_eq_on_core_of_integral_tendsto
    {μ : _root_.MeasureTheory.Measure X} {T : ℕ → Set X} (hT : ∀ n, MeasurableSet (T n))
    {e : X → ℝ} {en : ℕ → X → ℝ} (he : _root_.MeasureTheory.Integrable e μ)
    (hen : ∀ n, _root_.MeasureTheory.Integrable (en n) μ)
    {f : X → F} {fn : ℕ → X → F} (hf : _root_.MeasureTheory.Integrable f μ)
    (hfn : ∀ n, _root_.MeasureTheory.Integrable (fn n) μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * e x)
    (hboundn : ∀ n, ∀ᵐ x ∂μ, ‖fn n x‖ ≤ C * en n x)
    (hcore : ∀ n, en n =ᵐ[μ.restrict (T n)] e)
    (hcoref : ∀ n, fn n =ᵐ[μ.restrict (T n)] f)
    (henergy : _root_.Filter.Tendsto (fun n => ∫ x, en n x ∂μ) _root_.Filter.atTop (𝓝 (∫ x, e x ∂μ)))
    (htail : _root_.Filter.Tendsto (fun n => ∫ x in (T n)ᶜ, e x ∂μ) _root_.Filter.atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, fn n x ∂μ) _root_.Filter.atTop (𝓝 (∫ x, f x ∂μ)) := by
  have htailn : _root_.Filter.Tendsto (fun n => ∫ x in (T n)ᶜ, en n x ∂μ) _root_.Filter.atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫ x in (T n)ᶜ, en n x ∂μ) =
        (∫ x, en n x ∂μ) - (∫ x, e x ∂μ) + ∫ x in (T n)ᶜ, e x ∂μ := by
      have hn := _root_.MeasureTheory.integral_add_compl (hT n) (hen n)
      have h := _root_.MeasureTheory.integral_add_compl (hT n) he
      rw [_root_.MeasureTheory.integral_congr_ae (hcore n)] at hn
      linarith
    have h := (henergy.sub_const (∫ x, e x ∂μ)).add htail
    simpa only [sub_self, zero_add, ← heq] using h
  have htailfn (n : ℕ) : ‖∫ x in (T n)ᶜ, fn n x ∂μ‖ ≤
      C * ∫ x in (T n)ᶜ, en n x ∂μ := by
    calc
      _ ≤ ∫ x in (T n)ᶜ, C * en n x ∂μ :=
        _root_.MeasureTheory.norm_integral_le_of_norm_le ((hen n).restrict.const_mul C)
          (_root_.MeasureTheory.ae_restrict_of_ae (hboundn n))
      _ = _ := _root_.MeasureTheory.integral_const_mul _ _
  have htailf (n : ℕ) : ‖∫ x in (T n)ᶜ, f x ∂μ‖ ≤
      C * ∫ x in (T n)ᶜ, e x ∂μ := by
    calc
      _ ≤ ∫ x in (T n)ᶜ, C * e x ∂μ :=
        _root_.MeasureTheory.norm_integral_le_of_norm_le (he.restrict.const_mul C) (_root_.MeasureTheory.ae_restrict_of_ae hbound)
      _ = _ := _root_.MeasureTheory.integral_const_mul _ _
  have hdiff (n : ℕ) : (∫ x, fn n x ∂μ) - ∫ x, f x ∂μ =
      (∫ x in (T n)ᶜ, fn n x ∂μ) - ∫ x in (T n)ᶜ, f x ∂μ := by
    rw [← _root_.MeasureTheory.integral_add_compl (hT n) (hfn n), ← _root_.MeasureTheory.integral_add_compl (hT n) hf,
      _root_.MeasureTheory.integral_congr_ae (hcoref n)]
    abel
  have hlim : _root_.Filter.Tendsto (fun n => (∫ x, fn n x ∂μ) - ∫ x, f x ∂μ) _root_.Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show _root_.Filter.Tendsto (fun n => C * (∫ x in (T n)ᶜ, en n x ∂μ) +
        C * ∫ x in (T n)ᶜ, e x ∂μ) _root_.Filter.atTop (𝓝 0) by
        simpa only [_root_.MulZeroClass.mul_zero, add_zero] using (htailn.const_mul C).add (htail.const_mul C))
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add (htailfn n) (htailf n))
  simpa only [sub_add_cancel, zero_add] using hlim.add_const (∫ x, f x ∂μ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_of_eq_on_core_of_integral_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_of_eq_on_core_of_integral_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_of_eq_on_core_of_integral_tendsto ``Submission.MeasureTheory.tendsto_integral_of_eq_on_core_of_integral_tendsto

end MeasureTheory

end

end
