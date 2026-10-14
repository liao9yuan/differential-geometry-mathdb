import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.MeasureTheory

namespace DifferentialGeometry.Analysis.Integration

theorem integral_mul_deriv_mul_deriv_eq {u v P : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 2 u x)
    (hv : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 2 v x)
    (hP : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 1 P x) :
    (∫ x in a..b, u x * deriv (fun y => P y * deriv v y) x) =
      u b * (P b * deriv v b) - u a * (P a * deriv v a) -
        (v b * (P b * deriv u b) - v a * (P a * deriv u a)) +
      ∫ x in a..b, v x * deriv (fun y => P y * deriv u y) x := by
  have hu' : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 1 (deriv u) x :=
    fun x hx => (hu x hx).derivWithin (by norm_num)
  have hv' : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 1 (deriv v) x :=
    fun x hx => (hv x hx).derivWithin (by norm_num)
  have hPu : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 1 (fun y => P y * deriv u y) x :=
    fun x hx => (hP x hx).mul (hu' x hx)
  have hPv : ∀ x ∈ _root_.Set.uIcc a b, ContDiffAt ℝ 1 (fun y => P y * deriv v y) x :=
    fun x hx => (hP x hx).mul (hv' x hx)
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => ((hu x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => ((hPv x hx).differentiableAt (by norm_num)).hasDerivAt)
    (ContinuousOn.intervalIntegrable (fun x hx => (hu' x hx).continuousAt.continuousWithinAt))
    (ContinuousOn.intervalIntegrable (fun x hx =>
      ((hPv x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt))
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => ((hv x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x hx => ((hPu x hx).differentiableAt (by norm_num)).hasDerivAt)
    (ContinuousOn.intervalIntegrable (fun x hx => (hv' x hx).continuousAt.continuousWithinAt))
    (ContinuousOn.intervalIntegrable (fun x hx =>
      ((hPu x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt))
  have heq : (∫ x in a..b, deriv u x * (P x * deriv v x)) =
      ∫ x in a..b, deriv v x * (P x * deriv u x) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [h1, heq]
  rw [h2]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.integral_mul_deriv_mul_deriv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.integral_mul_deriv_mul_deriv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.integral_mul_deriv_mul_deriv_eq ``Submission.DifferentialGeometry.Analysis.Integration.integral_mul_deriv_mul_deriv_eq

end DifferentialGeometry.Analysis.Integration
