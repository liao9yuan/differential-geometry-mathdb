import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Topology _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasDerivAt_deriv_norm_sq {f : ℝ → E} {x : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    HasDerivAt (deriv (fun y => ‖f y‖ ^ 2))
      (2 * ‖deriv f x‖ ^ 2 + 2 * ⟪f x, deriv (deriv f) x⟫_ℝ) x := by
  have heq : deriv (fun y => ‖f y‖ ^ 2) =ᶠ[𝓝 x]
      fun y => 2 * ⟪f y, deriv f y⟫_ℝ := by
    filter_upwards [hf] with y hy
    exact hy.hasDerivAt.norm_sq.deriv
  have hd₀ := (hf.self_of_nhds.hasDerivAt.inner ℝ hf'.hasDerivAt).const_mul 2
  have hd := hd₀.congr_of_eventuallyEq heq
  have hvalue : 2 * ‖deriv f x‖ ^ 2 + 2 * ⟪f x, deriv (deriv f) x⟫_ℝ =
      2 * (⟪f x, deriv (deriv f) x⟫_ℝ + ⟪deriv f x, deriv f x⟫_ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [hvalue]
  exact hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_deriv_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_deriv_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_deriv_norm_sq ``Submission.DifferentialGeometry.Analysis.hasDerivAt_deriv_norm_sq

theorem deriv_deriv_norm_sq {f : ℝ → E} {x : ℝ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (deriv f) x) :
    deriv (deriv (fun y => ‖f y‖ ^ 2)) x =
      2 * ‖deriv f x‖ ^ 2 + 2 * ⟪f x, deriv (deriv f) x⟫_ℝ :=
  (hasDerivAt_deriv_norm_sq hf hf').deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.deriv_deriv_norm_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.deriv_deriv_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.deriv_deriv_norm_sq ``Submission.DifferentialGeometry.Analysis.deriv_deriv_norm_sq

end DifferentialGeometry.Analysis
