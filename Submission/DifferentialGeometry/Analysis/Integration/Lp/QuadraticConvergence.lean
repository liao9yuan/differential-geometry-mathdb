import Submission.DifferentialGeometry.Analysis.Integration.Lp.QuadraticLowerSemicontinuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.Filter _root_.Set
open scoped _root_.ENNReal _root_.Topology

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
theorem tendsto_integral_quadratic_of_tendsto
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B n t x y) μ)
    (hB₀ : ∀ x y, _root_.MeasureTheory.AEStronglyMeasurable (fun t => B₀ t x y) μ)
    (C : ℕ → ℝ) (C₀ : ℝ)
    (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C n)
    (hC₀ : ∀ᵐ t ∂μ, ‖B₀ t‖ ≤ C₀)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ t ∂μ, ‖B n t - B₀ t‖ ≤ δ)
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : _root_.MeasureTheory.Lp X 2 μ)
    (hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 u₀)) :
    _root_.Filter.Tendsto (fun n => ∫ t, B n t (u n t) (u n t) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ)) := by
  have hweak : ∀ F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀)) := fun F =>
    (F.continuous.tendsto u₀).comp hu
  have hcross := tendsto_integral_bilinear_of_weak
    B B₀ hB hB₀ C C₀ hC hC₀ hconv u u₀ u₀ hweak
  let K := _root_.Max.max 0 C₀ + 1
  have hK : 0 ≤ K := by positivity
  have hBbound : ∀ᶠ n in _root_.Filter.atTop, ∀ᵐ t ∂μ, ‖B n t‖ ≤ K := by
    filter_upwards [hconv 1 zero_lt_one] with n hn
    filter_upwards [hn, hC₀] with t ht ht₀
    calc
      ‖B n t‖ = ‖B n t - B₀ t + B₀ t‖ := by
        simpa only using! (congrArg _root_.Norm.norm (sub_add_cancel (B n t) (B₀ t))).symm
      _ ≤ ‖B n t - B₀ t‖ + ‖B₀ t‖ := by
        simpa only using! norm_add_le (B n t - B₀ t) (B₀ t)
      _ ≤ 1 + C₀ := add_le_add ht ht₀
      _ ≤ K := by dsimp only [K]; linarith only [le_max_right 0 C₀]
  have herrBound : ∀ᶠ n in _root_.Filter.atTop,
      ‖∫ t, B n t ((u n - u₀) t) (u n t) ∂μ‖ ≤
        K * (‖u n - u₀‖ * ‖u n‖) := by
    filter_upwards [hBbound] with n hn
    exact norm_integral_bilinear_le_lp_norm (B n) (hB n) hK hn (u n - u₀) (u n)
  have herrLimit : _root_.Filter.Tendsto (fun n => K * (‖u n - u₀‖ * ‖u n‖)) _root_.Filter.atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero] using
      ((hu.sub (tendsto_const_nhds (x := u₀))).norm.mul hu.norm).const_mul K
  have herr : _root_.Filter.Tendsto (fun n => ∫ t, B n t ((u n - u₀) t) (u n t) ∂μ)
      atTop (𝓝 0) := squeeze_zero_norm' herrBound herrLimit
  have heq (n : ℕ) :
      (∫ t, B n t ((u n - u₀) t) (u n t) ∂μ) +
        (∫ t, B n t (u₀ t) (u n t) ∂μ) =
      ∫ t, B n t (u n t) (u n t) ∂μ := by
    rw [← _root_.MeasureTheory.integral_add
      (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
        (Lp.memLp (u n - u₀)) (Lp.memLp (u n)))
      (integrable_bilinear_of_apply_aestronglyMeasurable (B n) (hB n) (hC n)
        (Lp.memLp u₀) (Lp.memLp (u n)))]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) u₀] with t ht
    simp only [ht, Pi.sub_apply, map_sub, sub_apply, sub_add_cancel]
  simpa only [heq, zero_add] using herr.add hcross

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_quadratic_of_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_quadratic_of_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_quadratic_of_tendsto ``Submission.MeasureTheory.tendsto_integral_quadratic_of_tendsto

end MeasureTheory

end

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.ENNReal _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

variable {P X : Type*} [MeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

open _root_.MeasureTheory in
theorem tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (B n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => B n t) _root_.Filter.atTop (𝓝 (B₀ t)))
    (u : ℕ → _root_.MeasureTheory.Lp X 2 μ) (u₀ : _root_.MeasureTheory.Lp X 2 μ)
    (hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 u₀)) :
    _root_.Filter.Tendsto (fun n => ∫ t, B n t (u n t) (u n t) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ)) := by
  have huweak (F : _root_.MeasureTheory.Lp X 2 μ →L[ℝ] ℝ) :
      Tendsto (fun n => F (u n)) _root_.Filter.atTop (𝓝 (F u₀)) :=
    (F.continuous.tendsto u₀).comp hu
  have hfixed := tendsto_integral_bilinear_of_weak_of_ae_tendsto
    B B₀ hB C hC hconv u u₀ u₀ huweak
  have hBapply (n : ℕ) (x y : X) :
      AEStronglyMeasurable (fun t => B n t x y) μ :=
    ((hB n).apply_continuousLinearMap x).apply_continuousLinearMap y
  have hC' (n : ℕ) : ∀ᵐ t ∂μ, ‖B n t‖ ≤ _root_.Max.max 0 C :=
    (hC n).mono fun t ht => ht.trans (le_max_right 0 C)
  have hdiff : _root_.Filter.Tendsto (fun n => ‖u n - u₀‖) _root_.Filter.atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hu.sub (tendsto_const_nhds (x := u₀))).norm
  have hbound : _root_.Filter.Tendsto (fun n => _root_.Max.max 0 C * (‖u n - u₀‖ * ‖u n‖)) _root_.Filter.atTop (𝓝 0) := by
    simpa only [_root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero] using (hdiff.mul hu.norm).const_mul (_root_.Max.max 0 C)
  have herr : _root_.Filter.Tendsto
      (fun n => (∫ t, B n t (u n t) (u n t) ∂μ) -
        ∫ t, B n t (u₀ t) (u n t) ∂μ) _root_.Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hbound
    have heq : (∫ t, B n t (u n t) (u n t) ∂μ) -
        (∫ t, B n t (u₀ t) (u n t) ∂μ) =
        ∫ t, B n t ((u n - u₀) t) (u n t) ∂μ := by
      rw [← _root_.MeasureTheory.integral_sub
        (integrable_bilinear_of_apply_aestronglyMeasurable
          (B n) (hBapply n) (hC n) (Lp.memLp (u n)) (Lp.memLp (u n)))
        (integrable_bilinear_of_apply_aestronglyMeasurable
          (B n) (hBapply n) (hC n) (Lp.memLp u₀) (Lp.memLp (u n)))]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [Lp.coeFn_sub (u n) u₀] with t ht
      rw [ht, Pi.sub_apply, map_sub, sub_apply]
    rw [heq]
    exact norm_integral_bilinear_le_lp_norm (B n) (hBapply n)
      (le_max_left 0 C) (hC' n) (u n - u₀) (u n)
  simpa only [sub_add_cancel, zero_add] using herr.add hfixed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto ``Submission.MeasureTheory.tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto

open _root_.MeasureTheory in
theorem tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (B n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ t ∂μ, ‖B n t‖ ≤ C)
    (hconv : ∀ᵐ t ∂μ, _root_.Filter.Tendsto (fun n => B n t) _root_.Filter.atTop (𝓝 (B₀ t)))
    (f : ℕ → P → X) (f₀ : P → X)
    (hf : ∀ n, _root_.MeasureTheory.MemLp (f n) 2 μ) (hf₀ : _root_.MeasureTheory.MemLp f₀ 2 μ)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun t => f n t - f₀ t) 2 μ) _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => ∫ t, B n t (f n t) (f n t) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ t, B₀ t (f₀ t) (f₀ t) ∂μ)) := by
  let u (n : ℕ) : _root_.MeasureTheory.Lp X 2 μ := (hf n).toLp (f n)
  let u₀ : _root_.MeasureTheory.Lp X 2 μ := hf₀.toLp f₀
  have hu : _root_.Filter.Tendsto u _root_.Filter.atTop (𝓝 u₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim
    have heq (n : ℕ) : ‖u n - u₀‖ =
        (_root_.MeasureTheory.eLpNorm (fun t => f n t - f₀ t) 2 μ).toReal := by
      change ‖(hf n).toLp (f n) - hf₀.toLp f₀‖ = _
      rw [← MemLp.toLp_sub (hf n) hf₀, Lp.norm_toLp]
      rfl
    simpa only [heq, ENNReal.toReal_zero, Function.comp_def] using hreal
  have h := tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto
    B B₀ hB hC hconv u u₀ hu
  have heq (n : ℕ) : (∫ t, B n t (u n t) (u n t) ∂μ) =
      ∫ t, B n t (f n t) (f n t) ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(hf n).coeFn_toLp] with t ht
    change B n t (((hf n).toLp (f n)) t) (((hf n).toLp (f n)) t) = _
    rw [ht]
  have heq₀ : (∫ t, B₀ t (u₀ t) (u₀ t) ∂μ) = ∫ t, B₀ t (f₀ t) (f₀ t) ∂μ := by
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hf₀.coeFn_toLp] with t ht
    change B₀ t ((hf₀.toLp f₀) t) ((hf₀.toLp f₀) t) = _
    rw [ht]
  simpa only [heq, heq₀] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto then
    throwError "Refusing to shadow existing declaration MeasureTheory.tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto ``Submission.MeasureTheory.tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto

end MeasureTheory

end
