import Submission.DifferentialGeometry.Geometry.Curvature.RegularizedDiskComparison
import Submission.DifferentialGeometry.Geometry.Curvature.DiskSectionalDensity
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Regularization.Integrability

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in




theorem integral_regularizedDisk_curvatureDensity_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall 0 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall 0 1, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ Metric.ball 0 1, diskMapTension g U q = 0)
    {a f : ℂ → ℝ} (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (han : ∀ z, 0 ≤ a z)
    (haeq : ∀ z ∈ Metric.closedBall 0 1, a =ᶠ[𝓝 z] diskMapConformalCoefficient g U)
    {ε : ℝ} (hε : ε ≠ 0) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I) ≤
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      regularizedConformalWeight a f ε z * diskMapSectionalDensity g U z) +
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      (1 - regularizedConformalWeight a f ε z) * (-Laplacian.laplacian f z)) := by
  let D := Metric.closedBall (0 : ℂ) 1
  have hD : IsCompact D := _root_.ProperSpace.isCompact_closedBall _ _
  have hB : _root_.MeasureTheory.IntegrableOn (diskMapSectionalDensity g U) D :=
    integrableOn_diskMapSectionalDensity g hs hU hD hDs hconf
  have hL : _root_.MeasureTheory.IntegrableOn (fun z => -Laplacian.laplacian f z) D :=
    (continuous_laplacian (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).neg.continuousOn.integrableOn_compact hD
  have hwB := integrable_regularizedConformalWeight_comp_mul (c := id) measurable_id
    ha.continuous.measurable hf.continuous.measurable (Eventually.of_forall han) hB ε
  have hwL := integrable_regularizedConformalWeight_comp_mul (c := id) measurable_id
    ha.continuous.measurable hf.continuous.measurable (Eventually.of_forall han) hL ε
  have hcL : _root_.MeasureTheory.IntegrableOn (fun z => (1 - regularizedConformalWeight a f ε z) *
      (-Laplacian.laplacian f z)) D := by
    convert hL.sub hwL using 1
    funext z
    simp only [Pi.sub_apply, id_eq]
    ring
  have hlog := contDiff_regularizedConformalLogFactor ha hf han hε
  have hK : _root_.MeasureTheory.IntegrableOn (fun z =>
      planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
        tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
          (x := z) (1 : ℂ) Complex.I) D := by
    have hcont : Continuous (fun z =>
        planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
          tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
            (x := z) (1 : ℂ) Complex.I) := by
      have heq : (fun z =>
          planeGaussianCurvature (regularizedConformalMetric a f ha hf han ε hε) z *
            tangentTwoJacobian (regularizedConformalMetric a f ha hf han ε hε)
              (x := z) (1 : ℂ) Complex.I) =
          (fun z : ℂ => -Laplacian.laplacian (regularizedConformalLogFactor a f ε) z) := by
        funext z
        exact planeGaussianCurvature_mul_areaDensity hlog z
      rw [heq]
      exact (continuous_laplacian (hlog.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).neg
    exact hcont.continuousOn.integrableOn_compact hD
  erw [← _root_.MeasureTheory.integral_add hwB hcL]
  apply _root_.MeasureTheory.integral_mono_ae hK (hwB.add hcL)
  have hsphere : ∀ᵐ z : ℂ, z ∉ Metric.sphere (0 : ℂ) 1 := by
    apply ae_iff.mpr
    convert Measure.addHaar_sphere _root_.MeasureTheory.MeasureSpace.volume (0 : ℂ) (1 : ℝ) using 1
    congr 1
    ext z
    simp
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_closedBall, _root_.MeasureTheory.ae_restrict_of_ae hsphere] with z hz hn
  have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
    have hle : ‖z‖ ≤ 1 := by simpa [D, Metric.mem_closedBall, dist_zero_right] using hz
    have hne : ‖z‖ ≠ 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hn
    simpa [Metric.mem_ball, dist_zero_right] using lt_of_le_of_ne hle hne
  exact regularizedDisk_curvatureDensity_le_sectional g Metric.isOpen_ball
    (hU.mono (Metric.ball_subset_closedBall.trans hDs))
    (fun q hq => hconf q (Metric.ball_subset_closedBall hq)) hharm ha hf han hε hzball (haeq z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integral_regularizedDisk_curvatureDensity_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integral_regularizedDisk_curvatureDensity_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integral_regularizedDisk_curvatureDensity_le ``Submission.DifferentialGeometry.Geometry.integral_regularizedDisk_curvatureDensity_le

end DifferentialGeometry.Geometry
