import Submission.DifferentialGeometry.Analysis.Calculus.Periodic.Smoothing
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission









noncomputable section

open _root_.MeasureTheory _root_.Filter _root_.Function _root_.ContinuousLinearMap _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Convolution

namespace DifferentialGeometry.Analysis

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]



theorem continuous_convolution_family {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {f : K × ℝ → F} (hf : Continuous f) :
    Continuous (fun p : K × ℝ => (k ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] (fun t => f (p.1, t))) p.2) := by
  let G : (K × ℝ) → ℝ → F := fun p t => k t • f (p.1, p.2 - t)
  have hG : Continuous G.uncurry := by
    apply Continuous.smul (hk.comp continuous_snd)
    exact hf.comp ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).sub continuous_snd))
  have hzero : ∀ p t, p ∈ (_root_.Set.univ : Set (K × ℝ)) → t ∉ tsupport k → G p t = 0 := by
    intro p t _ ht
    have hkt : k t = 0 := by
      by_contra hn
      exact ht (subset_closure hn)
    simp only [G, hkt, zero_smul]
  have hi := continuousOn_integral_of_compact_support hks hG.continuousOn hzero (μ := _root_.MeasureTheory.MeasureSpace.volume)
  simpa only [continuousOn_univ, G, _root_.MeasureTheory.convolution_def, _root_.ContinuousLinearMap.lsmul_apply] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_convolution_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_convolution_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_convolution_family ``Submission.DifferentialGeometry.Analysis.continuous_convolution_family

theorem hasCompactSupport_iteratedDeriv {k : ℝ → ℝ} (hk : HasCompactSupport k) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n k) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hk
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasCompactSupport_iteratedDeriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasCompactSupport_iteratedDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasCompactSupport_iteratedDeriv ``Submission.DifferentialGeometry.Analysis.hasCompactSupport_iteratedDeriv


theorem iteratedDeriv_convolution_left {k : ℝ → ℝ} (hk : ContDiff ℝ ∞ k)
    (hks : HasCompactSupport k) {f : ℝ → F} (hf : Continuous f) (n : ℕ) :
    iteratedDeriv n (k ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f) =
      (iteratedDeriv n k ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] f) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    funext x
    have hkn : ContDiff ℝ ∞ (iteratedDeriv n k) := by
      rw [iteratedDeriv_eq_iterate]
      exact hk.iterate_deriv n
    exact ((hasCompactSupport_iteratedDeriv hks n).hasDerivAt_convolution_left
      (_root_.ContinuousLinearMap.lsmul ℝ ℝ) (hkn.of_le (by simp)) hf.locallyIntegrable x).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.iteratedDeriv_convolution_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.iteratedDeriv_convolution_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.iteratedDeriv_convolution_left ``Submission.DifferentialGeometry.Analysis.iteratedDeriv_convolution_left


theorem continuous_iteratedDeriv_smoothPeriodic (φ : ContDiffBump (0 : ℝ))
    {f : K × ℝ → F} (hf : Continuous f) (n : ℕ) :
    Continuous (fun p : K × ℝ => iteratedDeriv n
      (smoothPeriodic φ (fun t => f (p.1, t))) p.2) := by
  have heq (p : K × ℝ) : iteratedDeriv n (smoothPeriodic φ (fun t => f (p.1, t))) =
      (iteratedDeriv n (φ.normed _root_.MeasureTheory.MeasureSpace.volume) ⋆[_root_.ContinuousLinearMap.lsmul ℝ ℝ, _root_.MeasureTheory.MeasureSpace.volume] (fun t => f (p.1, t))) :=
    iteratedDeriv_convolution_left φ.contDiff_normed φ.hasCompactSupport_normed
      (hf.comp (continuous_const.prodMk continuous_id)) n
  simp_rw [heq]
  apply continuous_convolution_family _ (hasCompactSupport_iteratedDeriv φ.hasCompactSupport_normed n) hf
  have hk : ContDiff ℝ ∞ (iteratedDeriv n (φ.normed _root_.MeasureTheory.MeasureSpace.volume)) := by
    rw [iteratedDeriv_eq_iterate]
    exact φ.contDiff_normed.iterate_deriv n
  exact hk.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic ``Submission.DifferentialGeometry.Analysis.continuous_iteratedDeriv_smoothPeriodic

end DifferentialGeometry.Analysis
