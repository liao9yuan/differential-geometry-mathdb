import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Complex.Norm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis


theorem gradient_complex_re (f : ℂ → ℝ) (z : ℂ) :
    (gradient f z).re = fderiv ℝ f z 1 := by
  have h := inner_gradient_left (f := f) (x := z) (y := (1 : ℂ))
  simpa only [Complex.inner, one_mul, Complex.conj_re] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.gradient_complex_re then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.gradient_complex_re"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.gradient_complex_re ``Submission.DifferentialGeometry.Analysis.gradient_complex_re


theorem gradient_complex_im (f : ℂ → ℝ) (z : ℂ) :
    (gradient f z).im = fderiv ℝ f z Complex.I := by
  have h := inner_gradient_left (f := f) (x := z) (y := Complex.I)
  simpa only [Complex.inner, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im, _root_.MulZeroClass.zero_mul, one_mul, zero_sub, neg_neg] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.gradient_complex_im then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.gradient_complex_im"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.gradient_complex_im ``Submission.DifferentialGeometry.Analysis.gradient_complex_im



theorem norm_gradient_sub_complex_sq (f g : ℂ → ℝ) (z : ℂ) :
    ‖gradient f z - gradient g z‖ ^ 2 =
      (fderiv ℝ f z 1 - fderiv ℝ g z 1) ^ 2 +
        (fderiv ℝ f z Complex.I - fderiv ℝ g z Complex.I) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, gradient_complex_re, gradient_complex_im]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_gradient_sub_complex_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_gradient_sub_complex_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_gradient_sub_complex_sq ``Submission.DifferentialGeometry.Analysis.norm_gradient_sub_complex_sq

end DifferentialGeometry.Analysis
