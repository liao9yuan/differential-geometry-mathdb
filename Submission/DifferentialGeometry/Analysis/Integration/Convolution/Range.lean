import Submission.DifferentialGeometry.Analysis.Integration.Integral.MeanNeighborhood
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.ContinuousLinearMap
open scoped _root_.Convolution

namespace IsCompact
open _root_.IsCompact

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure E) [μ.IsAddHaarMeasure]

open _root_.IsCompact in
theorem exists_normed_convolution_mem_of_integral_norm_sub_sq_lt
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∀ (φ : ContDiffBump (0 : E)) (q : ℝ), φ.rOut ≤ q * φ.rIn →
      ∀ (f : E → F) (x : E) (a : F),
      _root_.MeasureTheory.AEStronglyMeasurable f (μ.restrict (Metric.closedBall x φ.rOut)) →
      (∀ᵐ y ∂μ.restrict (Metric.closedBall x φ.rOut), f y ∈ K) →
      _root_.MeasureTheory.IntegrableOn (fun y => ‖f y - a‖ ^ 2) (Metric.closedBall x φ.rOut) μ →
      (q ^ Module.finrank ℝ E / μ.real (Metric.closedBall x φ.rOut)) *
        (∫ y in Metric.closedBall x φ.rOut, ‖f y - a‖ ^ 2 ∂μ) < δ ^ 2 →
      (φ.normed μ ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x ∈ U := by
  obtain ⟨δ, hδ, hbound⟩ :=
    hK.exists_integral_weighted_mem_of_integral_norm_sub_sq_lt (X := E) hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro φ q hφ f x a hf hfK hfi hsmall
  let k : E → ℝ := fun y => φ.normed μ (x - y)
  have hk : Measurable k :=
    φ.continuous_normed.measurable.comp (measurable_const.sub measurable_id)
  have hk0 (y : E) : 0 ≤ k y := φ.nonneg_normed _
  have hk1 : (∫ y, k y ∂μ) = 1 := by
    rw [show k = fun y => φ.normed μ (x - y) by rfl, ← _root_.MeasureTheory.integral_neg_eq_self]
    simp only [sub_neg_eq_add, _root_.MeasureTheory.integral_add_left_eq_self, ContDiffBump.integral_normed]
  have hsupport : Function.support k ⊆ Metric.closedBall x φ.rOut := by
    change Function.support ((ContDiffBump.normed φ μ) ∘ (fun y => x - y)) ⊆ _
    simp only [Function.support_comp_eq_preimage, ContDiffBump.support_normed_eq]
    intro y hy
    simp only [_root_.Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hy
    simpa [dist_eq_norm_sub'] using hy.le
  have hkC (y : E) (_hy : y ∈ Metric.closedBall x φ.rOut) :
      k y ≤ q ^ Module.finrank ℝ E / μ.real (Metric.closedBall x φ.rOut) := by
    rw [Measure.addHaar_real_closedBall_center]
    exact φ.normed_le_div_measure_closedBall_rOut μ q hφ (x - y)
  have hmem := hbound μ k (Metric.closedBall x φ.rOut)
    (q ^ Module.finrank ℝ E / μ.real (Metric.closedBall x φ.rOut)) f a
    hk hk0 hk1 measurableSet_closedBall hsupport hkC hf hfK hfi hsmall
  simpa only [_root_.MeasureTheory.convolution_eq_swap, _root_.ContinuousLinearMap.lsmul_apply, k] using hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `IsCompact.exists_normed_convolution_mem_of_integral_norm_sub_sq_lt then
    throwError "Refusing to shadow existing declaration IsCompact.exists_normed_convolution_mem_of_integral_norm_sub_sq_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `IsCompact.exists_normed_convolution_mem_of_integral_norm_sub_sq_lt ``Submission.IsCompact.exists_normed_convolution_mem_of_integral_norm_sub_sq_lt

end IsCompact

end
