import Submission.DifferentialGeometry.Analysis.Convex.UpperSupport
import Mathlib.Analysis.Calculus.Deriv.Shift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

theorem concaveOn_sub_quadratic_of_centered_upper_support
    {D : Set ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hsupport : ∀ x ∈ interior D, ∃ φ : ℝ → ℝ,
      ContDiffAt ℝ 2 φ 0 ∧ φ 0 = f x ∧
      (∀ᶠ r in 𝓝 (0 : ℝ), f (x + r) ≤ φ r) ∧ deriv (deriv φ) 0 ≤ C) :
    ConcaveOn ℝ D (fun t ↦ f t - C / 2 * t ^ 2) := by
  apply concaveOn_sub_quadratic_of_upper_support hD hf
  intro x hx
  obtain ⟨φ, hφ, htouch, hupper, hsecond⟩ := hsupport x hx
  have hshift : ContDiffAt ℝ 2 (fun r : ℝ ↦ r - x) x := by fun_prop
  have hφshift : ContDiffAt ℝ 2 (fun r : ℝ ↦ φ (r - x)) x := by
    have hφ' : ContDiffAt ℝ 2 φ (x - x) := by simpa only [sub_self] using hφ
    exact hφ'.fun_comp (f := fun r : ℝ ↦ r - x) x hshift
  refine ⟨fun r ↦ φ (r - x), hφshift, ?_, ?_, ?_⟩
  · simpa only [sub_self] using htouch
  · have hlim : _root_.Filter.Tendsto (fun r : ℝ ↦ r - x) (𝓝 x) (𝓝 (0 : ℝ)) := by
      simpa only [ContinuousAt, sub_self] using hshift.continuousAt
    filter_upwards [hlim.eventually hupper] with r hr
    have hcancel : x + (r - x) = r := by ring
    simpa only [hcancel] using hr
  · have hfirst : deriv (fun r : ℝ ↦ φ (r - x)) =
        (fun r : ℝ ↦ deriv φ (r - x)) := by
      funext r
      exact deriv_comp_sub_const φ x r
    rw [hfirst]
    have hsecond' : deriv (fun r : ℝ ↦ deriv φ (r - x)) x = deriv (deriv φ) (x - x) :=
      deriv_comp_sub_const (deriv φ) x x
    rw [hsecond']
    simpa only [sub_self] using hsecond

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support ``Submission.DifferentialGeometry.Analysis.concaveOn_sub_quadratic_of_centered_upper_support

end DifferentialGeometry.Analysis
