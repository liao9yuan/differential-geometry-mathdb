import Submission.DifferentialGeometry.Geometry.Metric.Radial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.InnerProductSpace

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem round_normal_inner_eq_radialBilinearForm (K : E →ₗᵢ[ℝ] F)
    {p : F} (hp : ‖p‖ = 1) (horth : ∀ v : E, ⟪p, K v⟫_ℝ = 0)
    {x : E} (hx : x ≠ 0) (v w : E) :
    let r := ‖x‖
    let D := fun v : E =>
      (-Real.sin (r / √2) * (⟪x, v⟫_ℝ / r / √2)) • p +
      ((Real.cos (r / √2) * (⟪x, v⟫_ℝ / r / √2) * r -
        Real.sin (r / √2) * (⟪x, v⟫_ℝ / r)) / r ^ 2) • K x +
      (Real.sin (r / √2) / r) • K v
    2 * ⟪D v, D w⟫_ℝ =
      radialBilinearForm (r⁻¹ • x) ((√2 * Real.sin (r / √2) / r) ^ 2) v w := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hroot : √(2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hroot2 : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have horth' (v : E) : ⟪K v, p⟫_ℝ = 0 := by rw [real_inner_comm, horth]
  dsimp only
  simp only [radialBilinearForm_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, K.inner_map_map,
    real_inner_self_eq_norm_sq, hp, horth, horth']
  rw [real_inner_comm v x]
  field_simp
  ring_nf
  have hroot4 : (√(2 : ℝ)) ^ 4 = 4 := by
    calc
      (√(2 : ℝ)) ^ 4 = ((√(2 : ℝ)) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hroot2]; norm_num
  rw [hroot2, hroot4]
  linear_combination
    2 * ⟪x, w⟫_ℝ * ‖x‖ ^ 2 * ⟪v, x⟫_ℝ *
      (Real.sin_sq_add_cos_sq (‖x‖ * (√2)⁻¹))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.round_normal_inner_eq_radialBilinearForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.round_normal_inner_eq_radialBilinearForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.round_normal_inner_eq_radialBilinearForm ``Submission.DifferentialGeometry.Geometry.Riemannian.round_normal_inner_eq_radialBilinearForm

end DifferentialGeometry.Geometry.Riemannian
