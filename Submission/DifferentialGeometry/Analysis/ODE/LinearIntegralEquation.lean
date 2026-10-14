import Submission.DifferentialGeometry.Analysis.ODE.Gronwall.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.ODE

theorem eq_exp_mul_of_integral_eq
    {T c x : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ}
    (hf : ContinuousOn f (_root_.Set.Icc 0 T))
    (heq : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      f t = x + ∫ s in (0 : ℝ)..t, c * f s) :
    ∀ t ∈ _root_.Set.Icc (0 : ℝ) T, f t = Real.exp (c * t) * x := by
  let g : ℝ → ℝ := fun t => Real.exp (c * t) * x
  have hg : Continuous g := by fun_prop
  have hgd (t : ℝ) : HasDerivAt g (c * g t) t := by
    simpa only [g, id_eq, mul_one, mul_assoc, mul_left_comm] using
      (((hasDerivAt_id t).const_mul c).exp.mul_const x)
  have hgi (t : ℝ) : g t = x + ∫ s in (0 : ℝ)..t, c * g s := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hgd s) ((continuous_const.mul hg).intervalIntegrable 0 t)
    rw [h]
    simp only [g, _root_.MulZeroClass.mul_zero, Real.exp_zero, one_mul]
    ring
  have hdiff (t : ℝ) (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
      f t - g t = ∫ s in (0 : ℝ)..t, c * (f s - g s) := by
    have hft : IntervalIntegrable (fun s => c * f s) _root_.MeasureTheory.MeasureSpace.volume 0 t :=
      ContinuousOn.intervalIntegrable_of_Icc ht.1
        ((continuousOn_const.mul hf).mono (_root_.Set.Icc_subset_Icc le_rfl ht.2))
    have hgt : IntervalIntegrable (fun s => c * g s) _root_.MeasureTheory.MeasureSpace.volume 0 t :=
      (continuous_const.mul hg).intervalIntegrable _ _
    rw [heq t ht, hgi t, show (fun s => c * (f s - g s)) =
      (fun s => c * f s - c * g s) by funext s; ring,
      intervalIntegral.integral_sub hft hgt]
    ring
  have hbound : ∀ t ∈ _root_.Set.Icc (0 : ℝ) T,
      ‖f t - g t‖ ≤ 0 + ‖c‖ * ∫ s in (0 : ℝ)..t, ‖f s - g s‖ := by
    intro t ht
    rw [hdiff t ht, zero_add]
    calc
      _ ≤ ∫ s in (0 : ℝ)..t, ‖c * (f s - g s)‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ = ‖c‖ * ∫ s in (0 : ℝ)..t, ‖f s - g s‖ := by
        simp only [norm_mul, intervalIntegral.integral_const_mul]
  have hgr := gronwall_integral_le hT (norm_nonneg c)
    ((hf.sub hg.continuousOn).norm) hbound
  intro t ht
  have hz : ‖f t - g t‖ = 0 := by
    have h := hgr t ht
    simp only [_root_.MulZeroClass.zero_mul] at h
    exact le_antisymm h (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.ODE.eq_exp_mul_of_integral_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.ODE.eq_exp_mul_of_integral_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.ODE.eq_exp_mul_of_integral_eq ``Submission.DifferentialGeometry.Analysis.ODE.eq_exp_mul_of_integral_eq

end DifferentialGeometry.Analysis.ODE
