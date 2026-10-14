import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.RegularizerLaplacian
import Submission.DifferentialGeometry.Analysis.Calculus.SmoothExtension.Ball
import Submission.DifferentialGeometry.Geometry.Curvature.ConformalPlane
import Submission.DifferentialGeometry.Geometry.Curvature.ConformalCircle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.InnerProductSpace _root_.Submission.InnerProductSpace _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Topology _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis






theorem exists_diskRegularizer_metric {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1)
    (hmass : ∫ w : ℂ, κ w = 2 * Real.pi) :
    ∃ (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F),
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, F =ᶠ[𝓝 z] diskRegularizerPotential κ) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        planeGaussianCurvature (conformalEuclideanMetric F hF) z *
          tangentTwoJacobian (conformalEuclideanMetric F hF) (x := z) (1 : ℂ) Complex.I = κ z) ∧
      (∀ z : ℂ, ‖z‖ = 1 → conformalCircleGeodesicCurvature F hF z = 0) := by
  obtain ⟨R, hR, hreg, hΔ⟩ := exists_diskRegularizer_poisson_neighborhood hc hκ hs
  obtain ⟨F, hF, _, heq⟩ := exists_contDiff_compactSupport_eq_near_closedBall
    (by norm_num : (0 : ℝ) ≤ 1) hR hreg
  refine ⟨F, hF, heq, ?_, ?_⟩
  · intro z hz
    rw [planeGaussianCurvature_mul_areaDensity hF,
      (_root_.InnerProductSpace.laplacian_congr_nhds (heq z hz)).eq_of_nhds,
      hΔ z (Metric.closedBall_subset_ball hR hz), neg_neg]
  · intro z hz
    have hzD : z ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, hz]
    have hfderiv : fderiv ℝ F z z = -1 := by
      have hpot := hasDerivAt_diskRegularizerPotential_radial_eq_neg_one hc hκ hs hmass hz
      have hcomp : HasDerivAt (fun r : ℝ => F (r • z)) (fderiv ℝ F z z) 1 := by
        simpa only [one_smul, id_eq] using!
          (hF.differentiable (by simp) ((1 : ℝ) • z)).hasFDerivAt.comp_hasDerivAt (1 : ℝ)
            ((hasDerivAt_id (1 : ℝ)).smul_const z)
      have hloc : (fun r : ℝ => F (r • z)) =ᶠ[𝓝 (1 : ℝ)]
          (fun r : ℝ => diskRegularizerPotential κ (r • z)) :=
        (heq z hzD).comp_tendsto (by
          convert! (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => z))).tendsto
            (1 : ℝ) using 1
          simp)
      exact (hcomp.congr_of_eventuallyEq hloc.symm).unique hpot
    rw [conformalCircleGeodesicCurvature_eq hF hz, hfderiv]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_diskRegularizer_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_diskRegularizer_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_diskRegularizer_metric ``Submission.DifferentialGeometry.Geometry.exists_diskRegularizer_metric

end DifferentialGeometry.Geometry
