import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Smoothing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.MeasureTheory _root_.Function _root_.ContinuousLinearMap
open scoped _root_.Convolution _root_.ContDiff

namespace DifferentialGeometry.Analysis


theorem smoothPeriodic_monotone (φ : ContDiffBump (0 : ℝ)) {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hm : Monotone ψ) : Monotone (smoothPeriodic φ ψ) := by
  have hi (x : ℝ) : _root_.MeasureTheory.Integrable (fun t => φ.normed _root_.MeasureTheory.MeasureSpace.volume t * ψ (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hc x
  intro x y hxy
  simp only [smoothPeriodic, _root_.MeasureTheory.convolution_def, _root_.ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact _root_.MeasureTheory.integral_mono (hi x) (hi y) (fun t =>
    mul_le_mul_of_nonneg_left (hm (sub_le_sub_right hxy t)) (φ.nonneg_normed t))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic_monotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic_monotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic_monotone ``Submission.DifferentialGeometry.Analysis.smoothPeriodic_monotone


theorem smoothPeriodic_affinePeriodic (φ : ContDiffBump (0 : ℝ)) {ψ : ℝ → ℝ}
    (hc : Continuous ψ) (hp : ∀ t, ψ (t + 1) = ψ t + 1) :
    ∀ t, smoothPeriodic φ ψ (t + 1) = smoothPeriodic φ ψ t + 1 := by
  have hi (x : ℝ) : _root_.MeasureTheory.Integrable (fun t => φ.normed _root_.MeasureTheory.MeasureSpace.volume t * ψ (x - t)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (_root_.ContinuousLinearMap.lsmul ℝ ℝ)
      φ.integrable_normed.locallyIntegrable hc x
  intro x
  simp only [smoothPeriodic, _root_.MeasureTheory.convolution_def, _root_.ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have heq : (fun t => φ.normed _root_.MeasureTheory.MeasureSpace.volume t * ψ (x + 1 - t)) =
      (fun t => φ.normed _root_.MeasureTheory.MeasureSpace.volume t * ψ (x - t) + φ.normed _root_.MeasureTheory.MeasureSpace.volume t) := by
    funext t
    rw [show x + 1 - t = (x - t) + 1 by ring, hp]
    ring
  rw [heq, _root_.MeasureTheory.integral_add (hi x) φ.integrable_normed, φ.integral_normed]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.smoothPeriodic_affinePeriodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.smoothPeriodic_affinePeriodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.smoothPeriodic_affinePeriodic ``Submission.DifferentialGeometry.Analysis.smoothPeriodic_affinePeriodic

end DifferentialGeometry.Analysis
