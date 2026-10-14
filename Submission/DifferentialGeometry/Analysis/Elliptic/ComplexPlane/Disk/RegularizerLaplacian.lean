import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.Distribution
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianConvolution
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.ImageHarmonic
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.RegularizerBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff _root_.Convolution

namespace DifferentialGeometry.Analysis



theorem logarithmicPotential_eq_convolution (κ : ℂ → ℝ) :
    logarithmicPotential κ = -(1 / (2 * Real.pi)) •
      ((fun z : ℂ => Real.log ‖z‖) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) := by
  funext z
  change -(1 / (2 * Real.pi)) *
      (κ ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun z : ℂ => Real.log ‖z‖)) z = _
  rw [_root_.MeasureTheory.convolution_eq_swap]
  simp only [Pi.smul_apply, smul_eq_mul, _root_.MeasureTheory.convolution_def, ContinuousLinearMap.mul_apply']
  congr 1
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with w
  exact mul_comm _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.logarithmicPotential_eq_convolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.logarithmicPotential_eq_convolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.logarithmicPotential_eq_convolution ``Submission.DifferentialGeometry.Analysis.logarithmicPotential_eq_convolution



theorem laplacian_logarithmicPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ 2 κ) (z : ℂ) :
    Laplacian.laplacian (logarithmicPotential κ) z = -κ z := by
  let k : ℂ → ℝ := fun w => Real.log ‖w‖
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hconv : ContDiff ℝ 2 (k ⋆[L] κ) :=
    hc.contDiff_convolution_right L locallyIntegrable_log_norm_complex hκ
  have htest : HasCompactSupport (fun w : ℂ => κ (z - w)) :=
    hc.comp_homeomorph (Homeomorph.subLeft z)
  have hsmooth : ContDiff ℝ 2 (fun w : ℂ => κ (z - w)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hfund := integral_log_norm_mul_laplacian htest hsmooth
  simp only [laplacian_comp_const_sub, sub_zero] at hfund
  rw [logarithmicPotential_eq_convolution, _root_.InnerProductSpace.laplacian_smul _ hconv.contDiffAt,
    laplacian_convolution_smooth_right locallyIntegrable_log_norm_complex hc hκ]
  change -(1 / (2 * Real.pi)) *
    (∫ w : ℂ, Real.log ‖w‖ * Laplacian.laplacian κ (z - w)) = -κ z
  rw [hfund]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_logarithmicPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_logarithmicPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_logarithmicPotential ``Submission.DifferentialGeometry.Analysis.laplacian_logarithmicPotential



theorem laplacian_diskRegularizerPotential {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ * R < 1)
    (hs : ∀ w ∈ tsupport κ, ‖w‖ ≤ ρ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    Laplacian.laplacian (diskRegularizerPotential κ) z = -κ z := by
  have hfirst : ContDiffAt ℝ 2 (logarithmicPotential κ) z :=
    (contDiff_logarithmicPotential hc hκ).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have himage : ContDiffAt ℝ 2 (diskImagePotential κ) z :=
    ((contDiffOn_diskImagePotential hc hκ hρ hρR hs z hz).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  change Laplacian.laplacian (logarithmicPotential κ + diskImagePotential κ) z = _
  rw [hfirst.laplacian_add himage, laplacian_logarithmicPotential hc
    (hκ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    laplacian_diskImagePotential hc hκ hρ hρR hs hz, add_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_diskRegularizerPotential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_diskRegularizerPotential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_diskRegularizerPotential ``Submission.DifferentialGeometry.Analysis.laplacian_diskRegularizerPotential



theorem exists_diskRegularizer_poisson_neighborhood {κ : ℂ → ℝ}
    (hc : HasCompactSupport κ) (hκ : ContDiff ℝ ∞ κ)
    (hs : tsupport κ ⊆ Metric.ball (0 : ℂ) 1) :
    ∃ R : ℝ, 1 < R ∧
      ContDiffOn ℝ ∞ (diskRegularizerPotential κ) (Metric.ball (0 : ℂ) R) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, Laplacian.laplacian (diskRegularizerPotential κ) z = -κ z := by
  obtain ⟨ρ, R, hρ, _, hR, hρR, hsρ⟩ := exists_disk_support_radii hc hs
  exact ⟨R, hR, contDiffOn_diskRegularizerPotential hc hκ hρ hρR hsρ,
    fun _ hz => laplacian_diskRegularizerPotential hc hκ hρ hρR hsρ hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.exists_diskRegularizer_poisson_neighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.exists_diskRegularizer_poisson_neighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.exists_diskRegularizer_poisson_neighborhood ``Submission.DifferentialGeometry.Analysis.exists_diskRegularizer_poisson_neighborhood

end DifferentialGeometry.Analysis
