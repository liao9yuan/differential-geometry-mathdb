import Submission.DifferentialGeometry.Analysis.Complex.Beltrami.Coefficient
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RealDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section
open scoped _root_.ComplexConjugate

namespace DifferentialGeometry.Analysis

def complexLinearPart (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1 - Complex.I * L Complex.I) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexLinearPart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexLinearPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexLinearPart ``Submission.DifferentialGeometry.Analysis.complexLinearPart

def complexAntilinearPart (L : ℂ →L[ℝ] ℂ) : ℂ := (L 1 + Complex.I * L Complex.I) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexAntilinearPart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexAntilinearPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexAntilinearPart ``Submission.DifferentialGeometry.Analysis.complexAntilinearPart

theorem apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj
    (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = complexLinearPart L * z + complexAntilinearPart L * conj z := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hz, map_add, map_smul, map_smul]
  apply Complex.ext <;>
    simp [complexLinearPart, complexAntilinearPart, Complex.mul_re, Complex.mul_im,
      Complex.real_smul] <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj ``Submission.DifferentialGeometry.Analysis.apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj

theorem beltrami_eq_iff_complex_linear_factor (L : ℂ →L[ℝ] ℂ) (μ : ℂ) :
    complexAntilinearPart L = μ * complexLinearPart L ↔
      ∀ z : ℂ, L z = complexLinearPart L * (z + μ * conj z) := by
  constructor
  · intro h z
    rw [apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj, h]
    ring
  · intro h
    have h1 := h 1
    have hI := h Complex.I
    have ha : complexAntilinearPart L = (L 1 + Complex.I * L Complex.I) / 2 := rfl
    rw [ha, h1, hI]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.beltrami_eq_iff_complex_linear_factor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.beltrami_eq_iff_complex_linear_factor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.beltrami_eq_iff_complex_linear_factor ``Submission.DifferentialGeometry.Analysis.beltrami_eq_iff_complex_linear_factor

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

theorem complexLinearPart_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    complexLinearPart (c • L) = c * complexLinearPart L := by
  simp only [complexLinearPart, smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexLinearPart_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexLinearPart_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexLinearPart_smul ``Submission.DifferentialGeometry.Analysis.complexLinearPart_smul

theorem complexAntilinearPart_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    complexAntilinearPart (c • L) = c * complexAntilinearPart L := by
  simp only [complexAntilinearPart, smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexAntilinearPart_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexAntilinearPart_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexAntilinearPart_smul ``Submission.DifferentialGeometry.Analysis.complexAntilinearPart_smul

theorem beltrami_fderiv_comp_holomorphic
    {W F : ℂ → ℂ} {z μ : ℂ} (hW : DifferentiableAt ℝ W z)
    (hF : DifferentiableAt ℂ F (W z))
    (hBel : complexAntilinearPart (fderiv ℝ W z) = μ * complexLinearPart (fderiv ℝ W z)) :
    complexAntilinearPart (fderiv ℝ (fun w => F (W w)) z) =
      μ * complexLinearPart (fderiv ℝ (fun w => F (W w)) z) := by
  have hh := (hF.hasDerivAt.complexToReal_fderiv.comp z hW.hasFDerivAt).fderiv
  have heq : fderiv ℝ (fun w => F (W w)) z = deriv F (W z) • fderiv ℝ W z := by
    change fderiv ℝ (fun w => F (W w)) z = _ at hh
    rw [hh]
    ext v
    simp
  rw [heq, complexAntilinearPart_smul, complexLinearPart_smul, hBel]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.beltrami_fderiv_comp_holomorphic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.beltrami_fderiv_comp_holomorphic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.beltrami_fderiv_comp_holomorphic ``Submission.DifferentialGeometry.Analysis.beltrami_fderiv_comp_holomorphic

end DifferentialGeometry.Analysis

end

end

section

noncomputable section
open scoped _root_.ComplexConjugate

namespace DifferentialGeometry.Analysis

theorem complexLinearPart_ne_zero_of_beltrami_of_ne_zero
    {L : ℂ →L[ℝ] ℂ} {μ : ℂ} (hL : L ≠ 0)
    (hBel : complexAntilinearPart L = μ * complexLinearPart L) : complexLinearPart L ≠ 0 := by
  intro ha
  apply hL
  ext z
  rw [apply_eq_complexLinearPart_mul_add_complexAntilinearPart_mul_conj, hBel, ha]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.complexLinearPart_ne_zero_of_beltrami_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.complexLinearPart_ne_zero_of_beltrami_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.complexLinearPart_ne_zero_of_beltrami_of_ne_zero ``Submission.DifferentialGeometry.Analysis.complexLinearPart_ne_zero_of_beltrami_of_ne_zero

theorem apply_eq_smul_of_same_beltrami
    (L K : ℂ →L[ℝ] ℂ) {μ : ℂ} (hK : K ≠ 0)
    (hLBel : complexAntilinearPart L = μ * complexLinearPart L)
    (hKBel : complexAntilinearPart K = μ * complexLinearPart K) (z : ℂ) :
    L z = (complexLinearPart L / complexLinearPart K) * K z := by
  have hα := complexLinearPart_ne_zero_of_beltrami_of_ne_zero hK hKBel
  rw [(beltrami_eq_iff_complex_linear_factor L μ).mp hLBel z,
    (beltrami_eq_iff_complex_linear_factor K μ).mp hKBel z]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.apply_eq_smul_of_same_beltrami then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.apply_eq_smul_of_same_beltrami"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.apply_eq_smul_of_same_beltrami ``Submission.DifferentialGeometry.Analysis.apply_eq_smul_of_same_beltrami

theorem comp_inverse_apply_eq_mul_of_same_beltrami
    (L : ℂ →L[ℝ] ℂ) (K : ℂ ≃L[ℝ] ℂ) {μ : ℂ}
    (hLBel : complexAntilinearPart L = μ * complexLinearPart L)
    (hKBel : complexAntilinearPart K.toContinuousLinearMap =
      μ * complexLinearPart K.toContinuousLinearMap) (z : ℂ) :
    L (K.symm z) = (complexLinearPart L / complexLinearPart K.toContinuousLinearMap) * z := by
  have hK : K.toContinuousLinearMap ≠ 0 := by
    intro hz
    have hh : K (1 : ℂ) = K 0 := by rw [map_zero]; exact congrArg (fun k : ℂ →L[ℝ] ℂ => k 1) hz
    exact one_ne_zero (K.injective hh)
  simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
    apply_eq_smul_of_same_beltrami L K.toContinuousLinearMap hK hLBel hKBel (K.symm z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.comp_inverse_apply_eq_mul_of_same_beltrami then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.comp_inverse_apply_eq_mul_of_same_beltrami"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.comp_inverse_apply_eq_mul_of_same_beltrami ``Submission.DifferentialGeometry.Analysis.comp_inverse_apply_eq_mul_of_same_beltrami

end DifferentialGeometry.Analysis

end

end
