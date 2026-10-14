import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.MeasureTheory _root_.MeasureTheory.Measure _root_.Filter _root_.Function _root_.Metric _root_.ContinuousLinearMap _root_.MeasureTheory.Measure.ContinuousLinearMap
open scoped _root_.Topology _root_.ContDiff _root_.Convolution _root_.NNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


def smoothPeriodic (φ : ContDiffBump (0 : ℝ)) (f : ℝ → F) : ℝ → F :=
  φ.normed _root_.MeasureTheory.MeasureSpace.volume ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic ``Submission.DifferentialGeometry.Analysis.smoothPeriodic

omit [CompleteSpace F] in
theorem smoothPeriodic_contDiff (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F}
    (hf : Continuous f) : ContDiff ℝ ∞ (smoothPeriodic φ f) := by
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hf.locallyIntegrable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic_contDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic_contDiff ``Submission.DifferentialGeometry.Analysis.smoothPeriodic_contDiff

omit [CompleteSpace F] in
theorem smoothPeriodic_periodic (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F} {T : ℝ}
    (hf : _root_.Function.Periodic f T) : _root_.Function.Periodic (smoothPeriodic φ f) T := by
  intro x
  simp only [smoothPeriodic, _root_.MeasureTheory.convolution_def, _root_.ContinuousLinearMap.lsmul_apply]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [show x + T - t = (x - t) + T by ring, hf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic_periodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic_periodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic_periodic ``Submission.DifferentialGeometry.Analysis.smoothPeriodic_periodic

@[simp] theorem smoothPeriodic_const (φ : ContDiffBump (0 : ℝ)) (v : F) :
    smoothPeriodic φ (fun _ => v) = fun _ => v := by
  funext x
  exact φ.normed_convolution_eq_right (fun _ _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic_const ``Submission.DifferentialGeometry.Analysis.smoothPeriodic_const


theorem dist_smoothPeriodic_le (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F}
    (hf : Continuous f) {x ε : ℝ}
    (h : ∀ y ∈ Metric.ball x φ.rOut, _root_.Dist.dist (f y) (f x) ≤ ε) :
    dist (smoothPeriodic φ f x) (f x) ≤ ε :=
  φ.dist_normed_convolution_le hf.aestronglyMeasurable h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.dist_smoothPeriodic_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.dist_smoothPeriodic_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.dist_smoothPeriodic_le ``Submission.DifferentialGeometry.Analysis.dist_smoothPeriodic_le

omit [CompleteSpace F] in
theorem smoothPeriodic_lipschitz (φ : ContDiffBump (0 : ℝ)) {f : ℝ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) : LipschitzWith C (smoothPeriodic φ f) := by
  have hi (x : ℝ) : _root_.MeasureTheory.Integrable (fun t => φ.normed _root_.MeasureTheory.MeasureSpace.volume t • f (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hf.continuous x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [smoothPeriodic, _root_.MeasureTheory.convolution_def, _root_.ContinuousLinearMap.lsmul_apply, dist_eq_norm]
  rw [← _root_.MeasureTheory.integral_sub (hi x) (hi y)]
  calc
    ‖∫ t, φ.normed _root_.MeasureTheory.MeasureSpace.volume t • f (x - t) - φ.normed _root_.MeasureTheory.MeasureSpace.volume t • f (y - t)‖ ≤
        ∫ t, φ.normed _root_.MeasureTheory.MeasureSpace.volume t * ((C : ℝ) * ‖x - y‖) := by
      apply _root_.MeasureTheory.norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _)
      filter_upwards [] with t
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed t)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed t)
      simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul (x - t) (y - t)
    _ = (C : ℝ) * ‖x - y‖ := by rw [_root_.MeasureTheory.integral_mul_const, φ.integral_normed, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic_lipschitz ``Submission.DifferentialGeometry.Analysis.smoothPeriodic_lipschitz

end DifferentialGeometry.Analysis
