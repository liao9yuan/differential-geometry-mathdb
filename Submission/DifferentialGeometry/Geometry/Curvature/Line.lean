import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem riemannOp_line_eq_zero (g : SmoothRiemannianMetric 𝓘(ℝ) ℝ)
    (t u v w : ℝ) : riemannOp (LeviCivita g) t u v w = 0 := by
  let A : ℝ →L[ℝ] ℝ →L[ℝ] ℝ →L[ℝ] ℝ := riemannOp (LeviCivita g) t
  have he : riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w = 0 := by
    have hs := riemannOp_swap (LeviCivita g) t (1 : ℝ) (1 : ℝ) w
    change (show ℝ from riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w) =
      -(show ℝ from riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w) at hs
    change (show ℝ from riemannOp (LeviCivita g) t (1 : ℝ) (1 : ℝ) w) = 0
    linarith
  change A 1 1 w = 0 at he
  change A u v w = 0
  calc
    A u v w = A (u • (1 : ℝ)) (v • (1 : ℝ)) w := by
          simp only [smul_eq_mul, mul_one]
    _ = u • (v • A 1 1 w) := by
      rw [map_smul, smul_apply, map_smul, smul_apply, smul_apply]
      exact _root_.SMulCommClass.smul_comm v u _
    _ = 0 := by rw [he, smul_zero, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.riemannOp_line_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.riemannOp_line_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.riemannOp_line_eq_zero ``Submission.DifferentialGeometry.Geometry.Curvature.riemannOp_line_eq_zero

theorem ricciTensor_line_eq_zero (g : SmoothRiemannianMetric 𝓘(ℝ) ℝ)
    (t u v : ℝ) : ricciTensor g t u v = 0 := by
  have he : ricciEndo g t u v = 0 := by
    apply LinearMap.ext
    intro w
    exact riemannOp_line_eq_zero g t w u v
  exact (congrArg (LinearMap.trace ℝ (TangentSpace 𝓘(ℝ) t)) he).trans (map_zero _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_line_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_line_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_line_eq_zero ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_line_eq_zero

end DifferentialGeometry.Geometry.Curvature
