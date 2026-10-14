import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Submission.MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X]

theorem exists_pos_integral_norm_sq_lt {τ : ℝ} (hτ : 0 < τ) (f : timeL2 X τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ∈ Set.Ioc 0 τ, ∀ T ∈ Set.Icc (0 : ℝ) δ,
      (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2) < ε := by
  have hf : _root_.MeasureTheory.IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Icc (0 : ℝ) τ) :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hcont : ContinuousOn
      (fun T : ℝ => ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2)
      (Set.Icc (0 : ℝ) τ) :=
    intervalIntegral.continuousOn_primitive_Icc hf
  obtain ⟨r, hr, hrbound⟩ :=
    Metric.continuousWithinAt_iff.1 (hcont 0 ⟨le_rfl, hτ.le⟩) ε hε
  let δ := _root_.Min.min τ (r / 2)
  have hδpos : 0 < δ := lt_min hτ (by linarith)
  have hδle : δ ≤ τ := min_le_left _ _
  refine ⟨δ, ⟨hδpos, hδle⟩, ?_⟩
  intro T hT
  have hTτ : T ∈ Set.Icc (0 : ℝ) τ := ⟨hT.1, hT.2.trans hδle⟩
  have hTr : _root_.Dist.dist T 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hT.1]
    have hδr : δ ≤ r / 2 := min_le_right _ _
    linarith [hT.2]
  have hbound := hrbound hTτ hTr
  have hnonneg : 0 ≤ ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 :=
    _root_.MeasureTheory.integral_nonneg (fun t => sq_nonneg ‖f t‖)
  have hzero : (∫ t in Set.Icc (0 : ℝ) (0 : ℝ), ‖f t‖ ^ 2) = 0 := by
    simp
  rw [hzero] at hbound
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_pos_integral_norm_sq_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_pos_integral_norm_sq_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_pos_integral_norm_sq_lt ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.exists_pos_integral_norm_sq_lt

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
