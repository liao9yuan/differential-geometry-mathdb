import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis

theorem det_complex_real_linearMap (A : ℂ →ₗ[ℝ] ℂ) :
    A.det = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI A, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.det_complex_real_linearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.det_complex_real_linearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.det_complex_real_linearMap ``Submission.DifferentialGeometry.Analysis.det_complex_real_linearMap

theorem exists_positive_triangular_decomposition
    (A : ℂ →ₗ[ℝ] ℂ) (hA : 0 < A.det) :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ s b : ℝ, 0 < b ∧
      ∀ z : ℂ, A z = a * (((z + (s * z.im : ℝ)).re : ℂ) +
        (b * (z + (s * z.im : ℝ)).im) • Complex.I) := by
  have ha : A 1 ≠ 0 := by
    intro h
    rw [det_complex_real_linearMap, h] at hA
    simp at hA
  let q := A Complex.I / A 1
  have hq : 0 < q.im := by
    have he : q.im = A.det / Complex.normSq (A 1) := by
      rw [det_complex_real_linearMap]
      dsimp [q]
      rw [Complex.div_im]
      ring
    rw [he]
    exact div_pos hA (Complex.normSq_pos.mpr ha)
  refine ⟨A 1, ha, q.re, q.im, hq, ?_⟩
  intro z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using z.re_add_im.symm
  have hAz : A z = (z.re : ℂ) * A 1 + (z.im : ℂ) * A Complex.I := by
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul]
    rfl
  have hcol : A Complex.I = A 1 * q := by
    dsimp [q]
    field_simp
  rw [hAz, hcol]
  have hreal : (z + (q.re * z.im : ℝ)).re = z.re + q.re * z.im := by simp
  have himag : (z + (q.re * z.im : ℝ)).im = z.im := by simp
  rw [hreal, himag]
  simp only [Complex.real_smul, Complex.ofReal_add, Complex.ofReal_mul]
  have hqrepr := q.re_add_im
  calc
    (z.re : ℂ) * A 1 + (z.im : ℂ) * (A 1 * q) =
        A 1 * ((z.re : ℂ) + (z.im : ℂ) * ((q.re : ℂ) + q.im * Complex.I)) := by
      rw [hqrepr]
      ring
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_positive_triangular_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_positive_triangular_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_positive_triangular_decomposition ``Submission.DifferentialGeometry.Analysis.exists_positive_triangular_decomposition

end DifferentialGeometry.Analysis
