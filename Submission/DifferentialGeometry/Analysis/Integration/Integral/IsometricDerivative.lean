import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory

namespace LinearIsometryEquiv
open _root_.LinearIsometryEquiv

open _root_.LinearIsometryEquiv in
theorem norm_fderiv_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → G) (x : E) :
    ‖fderiv ℝ (f ∘ e) x‖ = ‖fderiv ℝ f (e x)‖ := by
  have hd : fderiv ℝ (f ∘ e) x = (fderiv ℝ f (e x)).comp (e : E →L[ℝ] F) :=
    e.toContinuousLinearEquiv.comp_right_fderiv (f := f) (x := x)
  rw [hd]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearIsometryEquiv.norm_fderiv_comp then
    throwError "Refusing to shadow existing declaration LinearIsometryEquiv.norm_fderiv_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearIsometryEquiv.norm_fderiv_comp ``Submission.LinearIsometryEquiv.norm_fderiv_comp

open _root_.LinearIsometryEquiv in
theorem integral_norm_fderiv_sq_comp_closedBall
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → G) (r : ℝ) :
    (∫ x in Metric.closedBall (0 : E) r, ‖fderiv ℝ (f ∘ e) x‖ ^ 2) =
      ∫ y in Metric.closedBall (0 : F) r, ‖fderiv ℝ f y‖ ^ 2 := by
  simp_rw [e.norm_fderiv_comp]
  have h := e.measurePreserving.setIntegral_preimage_emb e.toMeasurableEquiv.measurableEmbedding
    (fun y => ‖fderiv ℝ f y‖ ^ 2) (Metric.closedBall (0 : F) r)
  have hset : e ⁻¹' Metric.closedBall (0 : F) r = Metric.closedBall (0 : E) r := by
    ext x
    simp only [_root_.Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, e.norm_map]
  rw [hset] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LinearIsometryEquiv.integral_norm_fderiv_sq_comp_closedBall then
    throwError "Refusing to shadow existing declaration LinearIsometryEquiv.integral_norm_fderiv_sq_comp_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `LinearIsometryEquiv.integral_norm_fderiv_sq_comp_closedBall ``Submission.LinearIsometryEquiv.integral_norm_fderiv_sq_comp_closedBall

end LinearIsometryEquiv
