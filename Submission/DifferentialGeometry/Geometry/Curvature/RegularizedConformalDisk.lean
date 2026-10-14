import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Boundary
import Submission.DifferentialGeometry.Geometry.Curvature.ConformalGaussBonnet

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Set _root_.MeasureTheory _root_.InnerProductSpace _root_.Submission.InnerProductSpace _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry


def regularizedConformalMetric (a f : ℂ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    (ε : ℝ) (hε : ε ≠ 0) : SmoothRiemannianMetric 𝓘(ℝ, ℂ) ℂ :=
  conformalEuclideanMetric (regularizedConformalLogFactor a f ε)
    (contDiff_regularizedConformalLogFactor ha hf han hε)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedConformalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedConformalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedConformalMetric ``Submission.DifferentialGeometry.Geometry.regularizedConformalMetric


theorem regularizedConformalMetric_inner {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (z v w : ℂ) :
    (regularizedConformalMetric a f ha hf han ε hε).inner z v w =
      regularizedConformalCoefficient a f ε z * _root_.Inner.inner ℝ v w := by
  rw [regularizedConformalMetric, conformalEuclideanMetric_inner,
    exp_two_regularizedConformalLogFactor (han z) hε]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedConformalMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedConformalMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedConformalMetric_inner ``Submission.DifferentialGeometry.Geometry.regularizedConformalMetric_inner



theorem regularizedConformalMetric_curvatureDensity {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I =
      -(1 / 2 : ℝ) * Laplacian.laplacian
        (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z := by
  rw [regularizedConformalMetric, planeGaussianCurvature_mul_areaDensity,
    laplacian_regularizedConformalLogFactor
      (ha.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (han z) hε]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity ``Submission.DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity



theorem regularizedConformalMetric_curvatureDensity_le {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I ≤
      (if a z = 0 then 0 else regularizedConformalWeight a f ε z *
        (-(1 / 2 : ℝ) * Laplacian.laplacian (fun q => Real.log (a q)) z)) +
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z) := by
  rw [regularizedConformalMetric_curvatureDensity ha hf han hε]
  exact regularizedConformal_curvature_le
    (ha.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (Filter.Eventually.of_forall han) hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity_le ``Submission.DifferentialGeometry.Geometry.regularizedConformalMetric_curvatureDensity_le



theorem regularizedConformalMetric_boundaryDensity {a f : ℂ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    {ε : ℝ} (hε : ε ≠ 0) {z : ℂ} (hz : ‖z‖ = 1)
    (hfν : fderiv ℝ f z z = -1) :
    conformalCircleGeodesicCurvature (regularizedConformalLogFactor a f ε)
        (contDiff_regularizedConformalLogFactor ha hf han hε) z *
      Real.sqrt ((regularizedConformalMetric a f ha hf han ε hε).inner z
        (Complex.I * z) (Complex.I * z)) =
      regularizedConformalWeight a f ε z *
        (1 + (1 / 2 : ℝ) * fderiv ℝ (fun q => Real.log (a q)) z z) := by
  rw [regularizedConformalMetric, conformalCircleGeodesicCurvature_mul_arclength _ hz]
  have hd : DifferentiableAt ℝ
      (fun q => Real.log (regularizedConformalCoefficient a f ε q)) z := by
    exact ((ha.differentiable (by simp) z).add
      (((hf.differentiable (by simp) z).const_mul 2).exp.const_mul (ε ^ 2))).log
        (regularizedConformalCoefficient_pos (f := f) (han z) hε).ne'
  unfold regularizedConformalLogFactor
  rw [(hd.hasFDerivAt.const_mul (1 / 2 : ℝ)).fderiv]
  exact regularizedConformal_boundary_density (ha.differentiable (by simp) z)
    (hf.differentiable (by simp) z) (Filter.Eventually.of_forall han) hfν hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.regularizedConformalMetric_boundaryDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.regularizedConformalMetric_boundaryDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.regularizedConformalMetric_boundaryDensity ``Submission.DifferentialGeometry.Geometry.regularizedConformalMetric_boundaryDensity

end DifferentialGeometry.Geometry
