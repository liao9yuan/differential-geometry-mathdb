import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.FundamentalSolution
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.InnerProductSpace
open scoped _root_.ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem gradient_re_eq_conj_deriv {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    gradient (fun y => (f y).re) z = conj (deriv f z) := by
  have hd := Complex.reCLM.hasFDerivAt.comp z hf.hasDerivAt.complexToReal_fderiv
  have hmap : Complex.reCLM.comp (deriv f z • (1 : ℂ →L[ℝ] ℂ)) =
      toDual ℝ ℂ (conj (deriv f z)) := by
    ext v
    simp [_root_.InnerProductSpace.toDual_apply_apply, Complex.inner, mul_comm]
  rw [hmap] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.gradient_re_eq_conj_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.gradient_re_eq_conj_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.gradient_re_eq_conj_deriv ``Submission.DifferentialGeometry.Analysis.gradient_re_eq_conj_deriv

theorem norm_gradient_re_eq_norm_deriv {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    ‖gradient (fun y => (f y).re) z‖ = ‖deriv f z‖ := by
  rw [gradient_re_eq_conj_deriv hf, Complex.norm_conj]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_gradient_re_eq_norm_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_gradient_re_eq_norm_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_gradient_re_eq_norm_deriv ``Submission.DifferentialGeometry.Analysis.norm_gradient_re_eq_norm_deriv

theorem gradient_log_norm_eq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hz : f z ≠ 0) :
    gradient (fun y => Real.log ‖f y‖) z =
      ((‖f z‖ ^ 2)⁻¹ : ℝ) • (conj (deriv f z) * f z) := by
  have hd := (hasFDerivAt_log_norm_complex hz).comp z hf.hasDerivAt.complexToReal_fderiv
  have hmap : ((‖f z‖ ^ 2)⁻¹ • innerSL ℝ (f z)).comp
        (deriv f z • (1 : ℂ →L[ℝ] ℂ)) =
      toDual ℝ ℂ (((‖f z‖ ^ 2)⁻¹ : ℝ) • (conj (deriv f z) * f z)) := by
    ext v
    change ((‖f z‖ ^ 2)⁻¹ : ℝ) * _root_.Inner.inner ℝ (f z) (deriv f z * v) =
      _root_.Inner.inner ℝ (((‖f z‖ ^ 2)⁻¹ : ℝ) • (conj (deriv f z) * f z)) v
    rw [real_inner_smul_left]
    congr 1
    simp [Complex.inner, mul_comm, mul_assoc]
  rw [hmap] at hd
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.gradient_log_norm_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.gradient_log_norm_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.gradient_log_norm_eq ``Submission.DifferentialGeometry.Analysis.gradient_log_norm_eq

theorem norm_deriv_eq_norm_mul_norm_gradient_log_norm {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hz : f z ≠ 0) :
    ‖deriv f z‖ = ‖f z‖ * ‖gradient (fun y => Real.log ‖f y‖) z‖ := by
  rw [gradient_log_norm_eq hf hz, norm_smul, norm_mul, Complex.norm_conj,
    Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hnorm : ‖f z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp [hnorm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_deriv_eq_norm_mul_norm_gradient_log_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_deriv_eq_norm_mul_norm_gradient_log_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_deriv_eq_norm_mul_norm_gradient_log_norm ``Submission.DifferentialGeometry.Analysis.norm_deriv_eq_norm_mul_norm_gradient_log_norm

end DifferentialGeometry.Analysis

end

end
