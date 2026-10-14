import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.GreenIdentity
import Submission.DifferentialGeometry.Geometry.Curvature.ConformalPlane
import Submission.DifferentialGeometry.Geometry.Curvature.ConformalCircle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.MeasureTheory _root_.InnerProductSpace _root_.Submission.InnerProductSpace _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis



theorem gaussBonnet_conformalDisk {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      planeGaussianCurvature (conformalEuclideanMetric f hf) z *
        tangentTwoJacobian (conformalEuclideanMetric f hf) (x := z) (1 : ℂ) Complex.I) +
    (∫ θ in -Real.pi..Real.pi,
      let z := Complex.polarCoord.symm (1, θ)
      conformalCircleGeodesicCurvature f hf z *
        Real.sqrt ((conformalEuclideanMetric f hf).inner z (Complex.I * z) (Complex.I * z))) =
      2 * Real.pi := by
  have hz (θ : ℝ) : ‖Complex.polarCoord.symm (1, θ)‖ = 1 := by
    simp
  simp only [planeGaussianCurvature_mul_areaDensity hf,
    conformalCircleGeodesicCurvature_mul_arclength hf (hz _)]
  rw [_root_.MeasureTheory.integral_neg, integral_laplacian_closedBall
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) (by norm_num)]
  simp only [one_mul]
  have hint : IntervalIntegrable (fun θ : ℝ =>
      fderiv ℝ f (Complex.polarCoord.symm (1, θ)) (Complex.polarCoord.symm (1, θ)))
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    exact ((hf.continuous_fderiv (by simp)).comp hp).clm_apply hp
  rw [intervalIntegral.integral_add intervalIntegrable_const hint,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.gaussBonnet_conformalDisk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.gaussBonnet_conformalDisk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.gaussBonnet_conformalDisk ``Submission.DifferentialGeometry.Geometry.gaussBonnet_conformalDisk

end DifferentialGeometry.Geometry
