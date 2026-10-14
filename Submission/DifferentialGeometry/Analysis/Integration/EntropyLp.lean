import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.MeasureTheory _root_.Filter
open scoped _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Integration


theorem abs_mul_log_le_one_add_rpow_div {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) :
    |x * Real.log x| ≤ 1 + x ^ (1 + δ) / δ := by
  have hpow : 0 ≤ x ^ (1 + δ) / δ :=
    div_nonneg (Real.rpow_nonneg hx _) hδ.le
  by_cases hx1 : x ≤ 1
  · rcases eq_or_lt_of_le hx with hx0 | hx0
    · simpa only [← hx0, _root_.MulZeroClass.zero_mul, abs_zero] using add_nonneg zero_le_one hpow
    · have hsmall : |x * Real.log x| < 1 := by
        simpa only [mul_comm] using Real.abs_log_mul_self_lt x hx0 hx1
      linarith
  · have hxpos : 0 < x := lt_trans zero_lt_one (lt_of_not_ge hx1)
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_not_ge hx1)
    rw [abs_of_nonneg (mul_nonneg hx hlog)]
    have hlarge := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx hδ) hx
    have hidentity : x * (x ^ δ / δ) = x ^ (1 + δ) / δ := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
      ring
    rw [hidentity] at hlarge
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.abs_mul_log_le_one_add_rpow_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.abs_mul_log_le_one_add_rpow_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.abs_mul_log_le_one_add_rpow_div ``Submission.DifferentialGeometry.Analysis.Integration.abs_mul_log_le_one_add_rpow_div

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


theorem integrable_mul_log_of_memLp [_root_.MeasureTheory.IsFiniteMeasure μ]
    {f : α → ℝ} {q : ℝ} (hq : 1 < q)
    (hf : _root_.MeasureTheory.MemLp f (ENNReal.ofReal q) μ) (hf0 : 0 ≤ᵐ[μ] f) :
    Integrable (fun x => f x * Real.log (f x)) μ := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq.le
  have hmoment : _root_.MeasureTheory.Integrable (fun x => ‖f x‖ ^ q) μ := by
    simpa only [ENNReal.toReal_ofReal hq0] using hf.integrable_norm_rpow'
  have hbound : _root_.MeasureTheory.Integrable (fun x => 1 + ‖f x‖ ^ q / (q - 1)) μ :=
    (_root_.MeasureTheory.integrable_const (1 : ℝ)).add (hmoment.div_const (q - 1))
  refine hbound.mono'
    (Real.continuous_mul_log.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  filter_upwards [hf0] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx, show 1 + (q - 1) = q by ring]
    using abs_mul_log_le_one_add_rpow_div hx (sub_pos.mpr hq)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.integrable_mul_log_of_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.integrable_mul_log_of_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.integrable_mul_log_of_memLp ``Submission.DifferentialGeometry.Analysis.Integration.integrable_mul_log_of_memLp


theorem integrable_sq_mul_log_sq_of_memLp [_root_.MeasureTheory.IsFiniteMeasure μ]
    {u : α → ℝ} {q : ℝ} (hq : 2 < q)
    (hu : _root_.MeasureTheory.MemLp u (ENNReal.ofReal q) μ) :
    Integrable (fun x => u x ^ 2 * Real.log (u x ^ 2)) μ := by
  have hsq : _root_.MeasureTheory.MemLp (fun x => u x ^ 2) (ENNReal.ofReal (q / 2)) μ := by
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs] using hu.norm_rpow_div 2
  exact integrable_mul_log_of_memLp (by linarith : 1 < q / 2) hsq
    (Eventually.of_forall fun x => sq_nonneg (u x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.integrable_sq_mul_log_sq_of_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.integrable_sq_mul_log_sq_of_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.integrable_sq_mul_log_sq_of_memLp ``Submission.DifferentialGeometry.Analysis.Integration.integrable_sq_mul_log_sq_of_memLp


theorem abs_sq_mul_log_sq_le {q : ℝ} (hq : 2 < q) (u : ℝ) :
    |u ^ 2 * Real.log (u ^ 2)| ≤ 1 + ‖u‖ ^ q / (q / 2 - 1) := by
  have hb := abs_mul_log_le_one_add_rpow_div (sq_nonneg u)
    (by linarith : 0 < q / 2 - 1)
  have heq : (u ^ 2) ^ (1 + (q / 2 - 1)) = ‖u‖ ^ q := by
    rw [show 1 + (q / 2 - 1) = q / 2 by ring,
      show u ^ 2 = ‖u‖ ^ (2 : ℝ) by simp [Real.norm_eq_abs],
      ← Real.rpow_mul (norm_nonneg u), show (2 : ℝ) * (q / 2) = q by ring]
  simpa only [heq] using hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.abs_sq_mul_log_sq_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.abs_sq_mul_log_sq_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.abs_sq_mul_log_sq_le ``Submission.DifferentialGeometry.Analysis.Integration.abs_sq_mul_log_sq_le


theorem tendsto_integral_sq_mul_log_sq_of_dominated [_root_.MeasureTheory.IsFiniteMeasure μ]
    {q : ℝ} (hq : 2 < q) {u : ℕ → α → ℝ} {v b : α → ℝ}
    (hb : _root_.MeasureTheory.MemLp b (ENNReal.ofReal q) μ)
    (hu : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (u n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖u n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => u n x) _root_.Filter.atTop (𝓝 (v x))) :
    _root_.Filter.Tendsto (fun n => ∫ x, u n x ^ 2 * Real.log (u n x ^ 2) ∂μ) _root_.Filter.atTop
      (𝓝 (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ)) := by
  have hq0 : 0 ≤ q := by linarith
  have hmoment : _root_.MeasureTheory.Integrable (fun x => ‖b x‖ ^ q) μ := by
    simpa only [ENNReal.toReal_ofReal hq0] using hb.integrable_norm_rpow'
  refine _root_.MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => 1 + ‖b x‖ ^ q / (q / 2 - 1))
    (fun n => Real.continuous_mul_log.comp_aestronglyMeasurable ((hu n).pow 2))
    ((_root_.MeasureTheory.integrable_const (1 : ℝ)).add (hmoment.div_const _)) ?_ ?_
  · intro n
    filter_upwards [hbound n] with x hx
    rw [Real.norm_eq_abs]
    refine (abs_sq_mul_log_sq_le hq (u n x)).trans ?_
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ q / 2 - 1)
    exact Real.rpow_le_rpow (norm_nonneg _) (hx.trans (le_abs_self (b x))) hq0
  · filter_upwards [hlim] with x hx
    exact Real.continuous_mul_log.continuousAt.tendsto.comp (hx.pow 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.tendsto_integral_sq_mul_log_sq_of_dominated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.tendsto_integral_sq_mul_log_sq_of_dominated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.tendsto_integral_sq_mul_log_sq_of_dominated ``Submission.DifferentialGeometry.Analysis.Integration.tendsto_integral_sq_mul_log_sq_of_dominated

end DifferentialGeometry.Analysis.Integration
