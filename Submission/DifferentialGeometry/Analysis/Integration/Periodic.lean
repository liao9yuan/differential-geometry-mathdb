import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.MeasureTheory

namespace Function.Periodic
open _root_.Function _root_.Function.Periodic

open _root_.Function _root_.Function.Periodic in
theorem intervalIntegral_le_period {f : ℝ → ℝ} {T a p q : ℝ}
    (hper : Function.Periodic f T) (hint : IntervalIntegrable f _root_.MeasureTheory.MeasureSpace.volume a (a + T))
    (hnn : ∀ x, 0 ≤ f x) (hqp : q ≤ p + T) :
    (∫ x in p..q, f x) ≤ ∫ x in a..a + T, f x := by
  by_cases hT : T = 0
  · subst T
    simp only [add_zero, intervalIntegral.integral_same] at hqp ⊢
    rw [intervalIntegral.integral_symm]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg hqp (fun x _ => hnn x))
  · have hall := hper.intervalIntegrable hT hint
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hall p q) (hall q (p + T))
    have hshift := hper.intervalIntegral_add_eq p a
    have hnonneg : 0 ≤ ∫ x in q..(p + T), f x :=
      intervalIntegral.integral_nonneg hqp (fun x _ => hnn x)
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.intervalIntegral_le_period then
    throwError "Refusing to shadow existing declaration Function.Periodic.intervalIntegral_le_period"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.intervalIntegral_le_period ``Submission.Function.Periodic.intervalIntegral_le_period

open _root_.Function _root_.Function.Periodic in
theorem exists_centered_intervalIntegral_eq {f : ℝ → ℝ} {T a r : ℝ}
    (hper : Function.Periodic f T) (hf : Continuous f) (hT : 0 ≤ T) (hr : 0 ≤ r)
    (hlen : r ≤ ∫ y in a..a + T, f y) (x : ℝ) :
    ∃ p q : ℝ, p ≤ x ∧ x ≤ q ∧ q ≤ p + T ∧
      (∫ y in p..x, f y) = r / 2 ∧ (∫ y in x..q, f y) = r / 2 ∧
        (∫ y in p..q, f y) = r := by
  have hperiod (y : ℝ) : (∫ z in y..y + T, f z) = ∫ z in a..a + T, f z :=
    hper.intervalIntegral_add_eq y a
  have hleft : (∫ y in (x - T)..x, f y) = ∫ y in a..a + T, f y := by
    simpa only [sub_add_cancel] using hperiod (x - T)
  have hfc : Continuous (fun p => ∫ y in p..x, f y) := by
    have heq : (fun p => ∫ y in p..x, f y) = fun p => -(∫ y in x..p, f y) := by
      funext p
      rw [intervalIntegral.integral_symm]
    rw [heq]
    exact (intervalIntegral.differentiable_integral_of_continuous hf).continuous.neg
  have hpimage : r / 2 ∈ (fun p => ∫ y in p..x, f y) '' _root_.Set.Icc (x - T) x := by
    apply intermediate_value_Icc' (sub_le_self x hT) hfc.continuousOn
    constructor
    · simpa only [intervalIntegral.integral_same] using (by linarith : 0 ≤ r / 2)
    · rw [hleft]
      linarith
  obtain ⟨p, hp, hpeq⟩ := hpimage
  change (∫ y in p..x, f y) = r / 2 at hpeq
  have hxp : x ≤ p + T := by linarith only [hp.1]
  have hright : r / 2 ≤ ∫ y in x..p + T, f y := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) p x) (hf.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) x (p + T))
    rw [hpeq, hperiod] at hadd
    linarith
  have hqimage : r / 2 ∈ (fun q => ∫ y in x..q, f y) '' _root_.Set.Icc x (p + T) := by
    apply intermediate_value_Icc hxp (intervalIntegral.differentiable_integral_of_continuous hf).continuous.continuousOn
    exact ⟨by simpa only [intervalIntegral.integral_same] using (by linarith : 0 ≤ r / 2), hright⟩
  obtain ⟨q, hq, hqeq⟩ := hqimage
  change (∫ y in x..q, f y) = r / 2 at hqeq
  refine ⟨p, q, hp.2, hq.1, hq.2, hpeq, hqeq, ?_⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) p x) (hf.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) x q)
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Function.Periodic.exists_centered_intervalIntegral_eq then
    throwError "Refusing to shadow existing declaration Function.Periodic.exists_centered_intervalIntegral_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `Function.Periodic.exists_centered_intervalIntegral_eq ``Submission.Function.Periodic.exists_centered_intervalIntegral_eq

end Function.Periodic
