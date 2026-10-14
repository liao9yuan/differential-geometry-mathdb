import Submission.DifferentialGeometry.Analysis.Spectral.FiniteDimensional.LeastEigenvector
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem eigenvalue_eq_of_lt_transverse_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (v : E) (b : ℝ)
    (hlower : ∀ x : E, ⟪v, x⟫_ℝ = 0 → b * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (u w : E) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {μ ν : ℝ}
    (heu : A u = μ • u) (hew : A w = ν • w) (hμ : μ < b) (hν : ν < b) :
    μ = ν := by
  by_contra hne
  have horth : ⟪u, w⟫_ℝ = 0 := by
    have hs := hA u w
    change ⟪A u, w⟫_ℝ = ⟪u, A w⟫_ℝ at hs
    rw [heu, hew, real_inner_smul_left, real_inner_smul_right] at hs
    exact (mul_eq_zero.mp (show (μ - ν) * ⟪u, w⟫_ℝ = 0 by nlinarith)).resolve_left
      (sub_ne_zero.mpr hne)
  have horth' : ⟪w, u⟫_ℝ = 0 := by rw [real_inner_comm, horth]
  let α := ⟪v, u⟫_ℝ
  let β := ⟪v, w⟫_ℝ
  have hα : α ≠ 0 := by
    intro hz
    have h := hlower u hz
    rw [heu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu] at h
    norm_num at h
    exact (not_le_of_gt hμ) h
  let x := β • u - α • w
  have hx : ⟪v, x⟫_ℝ = 0 := by
    simp only [x, inner_sub_right, real_inner_smul_right]
    change β * α - α * β = 0
    ring
  have hnorm : ‖x‖ ^ 2 = β ^ 2 + α ^ 2 := by
    simp only [x, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, hu, hw,
      real_inner_smul_left, real_inner_smul_right, horth, _root_.MulZeroClass.mul_zero, sub_zero, mul_one,
      sq_abs]
  have hform : ⟪A x, x⟫_ℝ = μ * β ^ 2 + ν * α ^ 2 := by
    simp only [x, map_sub, map_smul, heu, hew, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, horth, horth',
      real_inner_self_eq_norm_sq, hu, hw]
    ring
  have h := hlower x hx
  rw [hnorm, hform] at h
  nlinarith [mul_pos (sub_pos.mpr hν) (sq_pos_of_ne_zero hα),
    mul_nonneg (sub_nonneg.mpr hμ.le) (sq_nonneg β)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.eigenvalue_eq_of_lt_transverse_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.eigenvalue_eq_of_lt_transverse_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.eigenvalue_eq_of_lt_transverse_lower_bound ``Submission.DifferentialGeometry.Analysis.eigenvalue_eq_of_lt_transverse_lower_bound

end DifferentialGeometry.Analysis
