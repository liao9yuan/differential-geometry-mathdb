import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Width _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem initialRamp_speed_eq (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (lambda x t : ℝ) :
    (initialRamp γ).speed (fun _ => g) lambda x t =
      Real.sqrt (g.inner (loopLift γ x) (loopVelocity (I := I) γ x)
        (loopVelocity (I := I) γ x) + lambda ^ 2) := by
  rw [ProductCurve.speed, ProductCurve.inner, initialRamp_X_snd, mul_one, mul_one]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_eq

theorem initialRamp_speed_le (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q) (lambda x t : ℝ) :
    (initialRamp γ).speed (fun _ => g) lambda x t ≤
      Real.sqrt (g.inner (loopLift γ x) (loopVelocity (I := I) γ x)
        (loopVelocity (I := I) γ x)) + |lambda| := by
  rw [initialRamp_speed_eq]
  have hq := metric_inner_self_nonneg g (loopLift γ x) (loopVelocity (I := I) γ x)
  apply (Real.sqrt_le_iff).2
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hq, sq_abs lambda,
    mul_nonneg (Real.sqrt_nonneg (g.inner (loopLift γ x)
      (loopVelocity (I := I) γ x) (loopVelocity (I := I) γ x))) (abs_nonneg lambda)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_speed_le

theorem initialRamp_length_le (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) (lambda t : ℝ) :
    (initialRamp γ).length (fun _ => g) lambda t ≤
      loopLength g γ.toContinuousLoop + |lambda| := by
  let q : ℝ → ℝ := fun x => g.inner (loopLift γ.toContinuousLoop x)
    (loopVelocity (I := I) γ.toContinuousLoop x) (loopVelocity (I := I) γ.toContinuousLoop x)
  have hq : ContinuousOn q (_root_.Set.Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr
      ((DifferentialGeometry.metricQuad_cont g).comp γ.continuous_firstJet)
  have hr : ContinuousOn (fun x => (initialRamp γ).speed (fun _ => g) lambda x t)
      (_root_.Set.Icc (0 : ℝ) 1) := by
    simp_rw [initialRamp_speed_eq]
    exact (hq.add continuousOn_const).sqrt
  have hh : ContinuousOn (fun x => Real.sqrt (q x) + |lambda|) (_root_.Set.Icc (0 : ℝ) 1) :=
    hq.sqrt.add continuousOn_const
  have hle := intervalIntegral.integral_mono_on (μ := _root_.MeasureTheory.MeasureSpace.volume) zero_le_one
    (hr.intervalIntegrable_of_Icc zero_le_one)
    (hh.intervalIntegrable_of_Icc zero_le_one)
    (fun x _ => initialRamp_speed_le g γ.toContinuousLoop lambda x t)
  rw [intervalIntegral.integral_add
    (hq.sqrt.intervalIntegrable_of_Icc zero_le_one) intervalIntegrable_const,
    intervalIntegral.integral_const] at hle
  simp only [sub_zero, one_smul] at hle
  rw [ProductCurve.length, ProductCurve.integral]
  simp only [one_mul]
  change (∫ x in (0 : ℝ)..1, (initialRamp γ).speed (fun _ => g) lambda x t) ≤ _
  convert hle using 1
  rw [loopLength, ← _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc, ← intervalIntegral.integral_of_le zero_le_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le

theorem initialRamp_length_le_add_one (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) {lambda : ℝ} (hlambda : 0 ≤ lambda) (hlambda_one : lambda ≤ 1)
    (t : ℝ) :
    (initialRamp γ).length (fun _ => g) lambda t ≤ loopLength g γ.toContinuousLoop + 1 := by
  have h := initialRamp_length_le g γ lambda t
  rw [abs_of_nonneg hlambda] at h
  exact h.trans (add_le_add_right hlambda_one _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le_add_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le_add_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.initialRamp_length_le_add_one

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
