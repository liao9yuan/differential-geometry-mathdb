import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.Circle

theorem not_exists_continuous_logarithm :
    ¬ ∃ g : C(_root_.Circle, ℂ), ∀ z, Complex.exp (g z) = (z : ℂ) := by
  rintro ⟨g, hg⟩
  let a : ℝ → ℂ := fun t ↦ g (_root_.Circle.exp t) - g 1
  let b : ℝ → ℂ := fun t ↦ (t : ℂ) * Complex.I
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have he : (fun z ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ a =
      (fun z ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ b := by
    funext t
    apply Subtype.ext
    change Complex.exp (a t) = Complex.exp (b t)
    dsimp only [a, b]
    rw [Complex.exp_sub, hg, hg]
    simp only [_root_.Circle.coe_one, div_one, _root_.Circle.coe_exp]
  have heq := Complex.isCoveringMap_exp.eq_of_comp_eq ha hb he 0 (by simp [a, b])
  have hperiod := congrFun heq (2 * Real.pi)
  have hzero : (0 : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    simpa only [a, b, _root_.Circle.exp_two_pi, sub_self] using hperiod
  have him := congrArg Complex.im hzero
  simp only [Complex.zero_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.ofReal_im, Complex.I_re, mul_one, _root_.MulZeroClass.mul_zero, add_zero] at him
  linarith [Real.pi_pos]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Circle.not_exists_continuous_logarithm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Circle.not_exists_continuous_logarithm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Circle.not_exists_continuous_logarithm ``Submission.DifferentialGeometry.Topology.Circle.not_exists_continuous_logarithm

end DifferentialGeometry.Topology.Circle
