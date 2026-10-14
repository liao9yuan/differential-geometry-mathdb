import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Disk.LogKernel
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Filter _root_.InnerProductSpace _root_.Complex _root_.MeasureTheory
open scoped _root_.Topology _root_.RealInnerProductSpace _root_.Interval

namespace DifferentialGeometry.Analysis



theorem hasFDerivAt_log_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun x : ℂ => Real.log ‖x‖)
      ((‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hsq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hl := ((hasFDerivAt_id z).norm_sq.log hsq).const_mul (1 / 2 : ℝ)
  have heq : (fun x : ℂ => (1 / 2 : ℝ) * Real.log (‖x‖ ^ 2)) =
      (fun x : ℂ => Real.log ‖x‖) := by
    funext x
    rw [Real.log_pow]
    ring
  simp only [id_eq] at hl
  rw [heq] at hl
  convert! hl using 1
  ext v
  simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasFDerivAt_log_norm_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasFDerivAt_log_norm_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasFDerivAt_log_norm_complex ``Submission.DifferentialGeometry.Analysis.hasFDerivAt_log_norm_complex



theorem harmonicAt_log_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HarmonicAt (fun x : ℂ => Real.log ‖x‖) z := by
  exact (show AnalyticAt ℂ (fun x : ℂ => x) z by fun_prop).harmonicAt_log_norm hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.harmonicAt_log_norm_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.harmonicAt_log_norm_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.harmonicAt_log_norm_complex ``Submission.DifferentialGeometry.Analysis.harmonicAt_log_norm_complex



theorem laplacian_log_norm_complex {z : ℂ} (hz : z ≠ 0) :
    (Laplacian.laplacian (fun x : ℂ => Real.log ‖x‖)) z = 0 := by
  exact (harmonicAt_log_norm_complex hz).2.self_of_nhds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.laplacian_log_norm_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.laplacian_log_norm_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.laplacian_log_norm_complex ``Submission.DifferentialGeometry.Analysis.laplacian_log_norm_complex




theorem tendsto_self_mul_log_nhds_zero :
    Tendsto (fun r : ℝ => r * Real.log r) (𝓝 0) (𝓝 0) := by
  simpa using Real.continuous_mul_log.tendsto 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_self_mul_log_nhds_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_self_mul_log_nhds_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_self_mul_log_nhds_zero ``Submission.DifferentialGeometry.Analysis.tendsto_self_mul_log_nhds_zero



theorem hasDerivAt_log_norm_circleMap_radius {r θ : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r⁻¹ r := by
  have hlog : HasDerivAt Real.log |r|⁻¹ |r| :=
    Real.hasDerivAt_log (abs_ne_zero.mpr (ne_of_gt hr))
  have hcomp : HasDerivAt (Real.log ∘ abs) r⁻¹ r := by
    simpa only [abs_of_pos hr, mul_one] using hlog.comp r (hasDerivAt_abs_pos hr)
  exact hcomp.congr_of_eventuallyEq (Eventually.of_forall fun s => by
    simp only [Function.comp_apply, norm_circleMap_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_log_norm_circleMap_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_log_norm_circleMap_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_log_norm_circleMap_radius ``Submission.DifferentialGeometry.Analysis.hasDerivAt_log_norm_circleMap_radius




theorem disk_log_circle_radial_flux {r : ℝ} (hr : 0 < r) :
    ∫ θ in 0..2 * Real.pi,
      r * deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r = 2 * Real.pi := by
  have hd (θ : ℝ) : deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r = r⁻¹ :=
    (hasDerivAt_log_norm_circleMap_radius hr).deriv
  simp_rw [hd]
  rw [mul_inv_cancel₀ (ne_of_gt hr)]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.disk_log_circle_radial_flux then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.disk_log_circle_radial_flux"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.disk_log_circle_radial_flux ``Submission.DifferentialGeometry.Analysis.disk_log_circle_radial_flux



theorem tendsto_circleMap_intervalIntegral_nhds_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℂ → E) (hf : Continuous f) :
    _root_.Filter.Tendsto (fun r : ℝ => ∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ))
      (nhds 0) (nhds ((2 * Real.pi) • f 0)) := by
  have hjoint : Continuous (fun q : ℝ × ℝ => f (circleMap 0 q.1 q.2)) := by
    apply hf.comp
    unfold circleMap
    fun_prop
  have hc : Continuous (fun r : ℝ =>
      ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (circleMap 0 r θ)) :=
    continuous_parametric_integral_of_continuous hjoint _root_.CompactIccSpace.isCompact_Icc
  have hle : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have heq (r : ℝ) :
      (∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ)) =
        ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (circleMap 0 r θ) := by
    rw [intervalIntegral.integral_of_le hle]
    exact _root_.MeasureTheory.setIntegral_congr_set (_root_.MeasureTheory.Ioc_ae_eq_Icc (α := ℝ) (μ := _root_.MeasureTheory.MeasureSpace.volume))
  have hzero : (∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi), f (circleMap 0 0 θ)) =
      (2 * Real.pi) • f 0 := by
    simp [circleMap, hle]
  rw [← hzero]
  exact (hc.tendsto 0).congr' (Eventually.of_forall fun r => (heq r).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_circleMap_intervalIntegral_nhds_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_circleMap_intervalIntegral_nhds_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_circleMap_intervalIntegral_nhds_zero ``Submission.DifferentialGeometry.Analysis.tendsto_circleMap_intervalIntegral_nhds_zero



theorem tendsto_disk_log_radial_flux_mul_nhdsGT_zero
    (f : ℂ → ℝ) (hf : Continuous f) :
    _root_.Filter.Tendsto (fun r : ℝ => ∫ θ in 0..2 * Real.pi,
      (r * deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r) *
        f (circleMap 0 r θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * Real.pi) * f 0)) := by
  have hbase : _root_.Filter.Tendsto (fun r : ℝ => ∫ θ in 0..2 * Real.pi, f (circleMap 0 r θ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * Real.pi) * f 0)) := by
    simpa only [smul_eq_mul] using (tendsto_circleMap_intervalIntegral_nhds_zero f hf).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  have hd (θ : ℝ) : deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r = r⁻¹ :=
    (hasDerivAt_log_norm_circleMap_radius hrpos).deriv
  apply intervalIntegral.integral_congr
  intro θ _
  change f (circleMap 0 r θ) =
    r * deriv (fun s : ℝ => Real.log ‖circleMap 0 s θ‖) r * f (circleMap 0 r θ)
  rw [hd, mul_inv_cancel₀ (ne_of_gt hrpos), one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_disk_log_radial_flux_mul_nhdsGT_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_disk_log_radial_flux_mul_nhdsGT_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_disk_log_radial_flux_mul_nhdsGT_zero ``Submission.DifferentialGeometry.Analysis.tendsto_disk_log_radial_flux_mul_nhdsGT_zero

end DifferentialGeometry.Analysis
