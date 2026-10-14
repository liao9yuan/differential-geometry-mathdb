import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sub_le_of_norm_deriv_le_rpow {f : ℝ → E} {T C r : ℝ}
    (hT : 0 ≤ T) (hr : -1 < r) (hf : ContinuousOn f (_root_.Set.Icc 0 T))
    (hfd : DifferentiableOn ℝ f (_root_.Set.Ioo 0 T))
    (hbound : ∀ᵐ s : ℝ, s ∈ _root_.Set.Ioo 0 T → ‖deriv f s‖ ≤ C * s ^ r) :
    ‖f T - f 0‖ ≤ C * T ^ (r + 1) / (r + 1) := by
  have h := norm_sub_le_integral_of_norm_deriv_le_of_le hT hf hfd hbound
    ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul C)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero] at h
  exact h.trans_eq (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_le_rpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_le_rpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_le_rpow ``Submission.DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_le_rpow

theorem norm_sub_le_of_norm_deriv_sq_le_inv {f : ℝ → E} {T A : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hf : ContinuousOn f (_root_.Set.Icc 0 T))
    (hfd : DifferentiableOn ℝ f (_root_.Set.Ioo 0 T))
    (hbound : ∀ s ∈ _root_.Set.Ioo 0 T, ‖deriv f s‖ ^ 2 ≤ A / s) :
    ‖f T - f 0‖ ≤ 2 * Real.sqrt (A * T) := by
  have hb : ∀ᵐ s : ℝ, s ∈ _root_.Set.Ioo 0 T →
      ‖deriv f s‖ ≤ Real.sqrt A * s ^ (-(1 / 2 : ℝ)) := by
    apply _root_.MeasureTheory.ae_of_all
    intro s hs
    calc
      ‖deriv f s‖ = Real.sqrt (‖deriv f s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (A / s) := Real.sqrt_le_sqrt (hbound s hs)
      _ = Real.sqrt A * s ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_div hA, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have h := norm_sub_le_of_norm_deriv_le_rpow hT (by norm_num : -1 < -(1 / 2 : ℝ)) hf hfd hb
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
  rw [← Real.sqrt_eq_rpow] at h
  exact h.trans_eq (by rw [Real.sqrt_mul hA]; ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_sq_le_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_sq_le_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_sq_le_inv ``Submission.DifferentialGeometry.Analysis.norm_sub_le_of_norm_deriv_sq_le_inv

theorem norm_sub_le_integral_norm_deriv_of_mem_Icc {f : ℝ → E} {a b x y : ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc a b)) (hfd : DifferentiableOn ℝ f (_root_.Set.Ioo a b))
    (hi : IntervalIntegrable (fun s => ‖deriv f s‖) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hx : x ∈ _root_.Set.Icc a b) (hy : y ∈ _root_.Set.Icc a b) :
    ‖f x - f y‖ ≤ ∫ s in a..b, ‖deriv f s‖ := by
  have hordered {u v : ℝ} (hu : u ∈ _root_.Set.Icc a b) (hv : v ∈ _root_.Set.Icc a b) (huv : u ≤ v) :
      ‖f v - f u‖ ≤ ∫ s in a..b, ‖deriv f s‖ := by
    have hint : IntervalIntegrable (fun s => ‖deriv f s‖) _root_.MeasureTheory.MeasureSpace.volume u v := by
      apply hi.mono_set
      rw [_root_.Set.uIcc_of_le huv, _root_.Set.uIcc_of_le (hu.1.trans hu.2)]
      exact _root_.Set.Icc_subset_Icc hu.1 hv.2
    have h := norm_sub_le_integral_of_norm_deriv_le_of_le huv
      (hf.mono (_root_.Set.Icc_subset_Icc hu.1 hv.2))
      (hfd.mono (_root_.Set.Ioo_subset_Ioo hu.1 hv.2)) (_root_.MeasureTheory.ae_of_all _ (fun _ _ => le_rfl)) hint
    exact h.trans (intervalIntegral.integral_mono_interval hu.1 huv hv.2
      (_root_.MeasureTheory.ae_of_all _ (fun s => norm_nonneg (deriv f s))) hi)
  rcases le_total x y with hxy | hyx
  · rw [norm_sub_rev]
    exact hordered hx hy hxy
  · exact hordered hy hx hyx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_sub_le_integral_norm_deriv_of_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_sub_le_integral_norm_deriv_of_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_sub_le_integral_norm_deriv_of_mem_Icc ``Submission.DifferentialGeometry.Analysis.norm_sub_le_integral_norm_deriv_of_mem_Icc

end DifferentialGeometry.Analysis
