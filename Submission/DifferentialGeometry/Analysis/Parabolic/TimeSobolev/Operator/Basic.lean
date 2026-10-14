import Submission.DifferentialGeometry.Analysis.Integration.Lp.Operator
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T : ℝ}

theorem memLp_timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    MemLp (fun t => A t (f t)) 2 (timeMeasure T) :=
  (Lp.memLp f).clm_apply_of_bound A (fun v => hA.apply_continuousLinearMap v) hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.memLp_timeOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.memLp_timeOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.memLp_timeOp ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.memLp_timeOp

noncomputable def timeOp
    (A : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    timeL2 X T →L[ℝ] timeL2 Y T :=
  Lp.multiplicationOperator A (fun v => hA.apply_continuousLinearMap v) C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp

theorem timeOp_apply_ae
    (A : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (f : timeL2 X T) :
    timeOp A hA C hC f =ᵐ[timeMeasure T] fun t => A t (f t) :=
  Lp.multiplicationOperator_apply_ae A (fun v => hA.apply_continuousLinearMap v) C hC f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_apply_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_apply_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_apply_ae ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_apply_ae

theorem timeOp_norm_le
    (A : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ)) :
    ‖timeOp A hA C hC‖ ≤ (C : ℝ) :=
  Lp.multiplicationOperator_norm_le A (fun v => hA.apply_continuousLinearMap v) C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_norm_le

theorem timeOp_sub
    (A B : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (hB : _root_.MeasureTheory.AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    timeOp A hA CA hCA - timeOp B hB CB hCB =
      timeOp (fun t ↦ A t - B t) (hA.sub hB) C hC := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (timeOp A hA CA hCA f) (timeOp B hB CB hCB f),
    timeOp_apply_ae A hA CA hCA f, timeOp_apply_ae B hB CB hCB f,
    timeOp_apply_ae (fun t ↦ A t - B t) (hA.sub hB) C hC f]
    with t hsub hAf hBf hDf
  change ((timeOp A hA CA hCA f - timeOp B hB CB hCB f : timeL2 Y T) : ℝ → Y) t = _
  rw [hsub, Pi.sub_apply, hAf, hBf, hDf, sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub

theorem timeOp_sub_norm_le
    (A B : ℝ → X →L[ℝ] Y)
    (hA : _root_.MeasureTheory.AEStronglyMeasurable A (timeMeasure T))
    (hB : _root_.MeasureTheory.AEStronglyMeasurable B (timeMeasure T))
    (CA CB C : NNReal)
    (hCA : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (CA : ℝ))
    (hCB : ∀ᵐ t ∂timeMeasure T, ‖B t‖ ≤ (CB : ℝ))
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t - B t‖ ≤ (C : ℝ)) :
    ‖timeOp A hA CA hCA - timeOp B hB CB hCB‖ ≤ (C : ℝ) := by
  rw [timeOp_sub A B hA hB CA CB C hCA hCB hC]
  exact timeOp_norm_le _ _ C hC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub_norm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub_norm_le ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeOp_sub_norm_le


end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
