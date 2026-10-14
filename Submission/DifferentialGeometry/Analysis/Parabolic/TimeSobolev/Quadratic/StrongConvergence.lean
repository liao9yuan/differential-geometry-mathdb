import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.WeakConvergence
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

theorem timeQuad_strong
    (A : ℕ → ℝ → X →L[ℝ] X) (A_lim : ℝ → X →L[ℝ] X)
    (hA : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (A n) (timeMeasure T))
    (hA_lim : _root_.MeasureTheory.AEStronglyMeasurable A_lim (timeMeasure T))
    (C : ℕ → NNReal) (C_lim : NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (hC_lim : ∀ᵐ t ∂timeMeasure T, ‖A_lim t‖ ≤ (C_lim : ℝ))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in _root_.Filter.atTop,
      ∀ᵐ t ∂timeMeasure T, ‖A n t - A_lim t‖ ≤ δ)
    (u : ℕ → timeL2 X T) (u_lim : timeL2 X T)
    (hu : _root_.Filter.Tendsto u _root_.Filter.atTop (nhds u_lim)) :
    _root_.Filter.Tendsto (fun n ↦ timeQuad (A n) (hA n) (C n) (hC n) (u n)) _root_.Filter.atTop
      (nhds (timeQuad A_lim hA_lim C_lim hC_lim u_lim)) := by
  let v : ℕ → timeL2 X T :=
    fun n ↦ timeOp (A n) (hA n) (C n) (hC n) (u n)
  let v_lim : timeL2 X T := timeOp A_lim hA_lim C_lim hC_lim u_lim
  have hu_weak : ∀ z, _root_.Filter.Tendsto (fun n ↦ _root_.Inner.inner ℝ (u n) z) _root_.Filter.atTop
      (nhds (_root_.Inner.inner ℝ u_lim z)) := fun z ↦ hu.inner tendsto_const_nhds
  have hv_weak : ∀ z, _root_.Filter.Tendsto (fun n ↦ _root_.Inner.inner ℝ (v n) z) _root_.Filter.atTop
      (nhds (_root_.Inner.inner ℝ v_lim z)) := by
    simpa only [v, v_lim] using
      timeOp_weak_uniform A A_lim hA hA_lim C C_lim hC hC_lim hconv
        u u_lim hu_weak
  obtain ⟨D, hvD⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (v n)) fun z ↦ by
    simpa only [innerSL_apply_apply, _root_.Set.forall_mem_range] using
      (isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto (fun n ↦ _root_.Inner.inner ℝ (v n) z) (hv_weak z)))
  have hv_norm (n : ℕ) : ‖v n‖ ≤ D := by
    simpa only [innerSL_apply_norm] using hvD n
  have hdiff : _root_.Filter.Tendsto (fun n ↦ u n - u_lim) _root_.Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hu.sub_const u_lim
  have hdiff_norm : _root_.Filter.Tendsto (fun n ↦ ‖u n - u_lim‖) _root_.Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.1 hdiff
  have herr_bound (n : ℕ) :
      |inner ℝ (v n) (u n - u_lim)| ≤ D * ‖u n - u_lim‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hv_norm n) (norm_nonneg _))
  have herr_abs : _root_.Filter.Tendsto (fun n ↦ |_root_.Inner.inner ℝ (v n) (u n - u_lim)|) _root_.Filter.atTop
      (nhds 0) := by
    apply squeeze_zero (fun n ↦ abs_nonneg _) herr_bound
    simpa only [_root_.MulZeroClass.mul_zero] using hdiff_norm.const_mul D
  have herr : _root_.Filter.Tendsto (fun n ↦ _root_.Inner.inner ℝ (v n) (u n - u_lim)) _root_.Filter.atTop
      (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 herr_abs
  change _root_.Filter.Tendsto (fun n ↦ _root_.Inner.inner ℝ (v n) (u n)) _root_.Filter.atTop
    (nhds (_root_.Inner.inner ℝ v_lim u_lim))
  rw [show (fun n ↦ _root_.Inner.inner ℝ (v n) (u n)) =
      (fun n ↦ _root_.Inner.inner ℝ (v n) u_lim + _root_.Inner.inner ℝ (v n) (u n - u_lim)) by
    funext n
    rw [inner_sub_right]
    ring]
  simpa only [add_zero] using (hv_weak u_lim).add herr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_strong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_strong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_strong ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeQuad_strong

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
