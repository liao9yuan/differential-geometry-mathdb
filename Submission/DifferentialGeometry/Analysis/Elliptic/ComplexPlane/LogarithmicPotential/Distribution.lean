import Submission.DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.GreenIdentity
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.FundamentalSolution
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LogarithmicPotential.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission







noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.InnerProductSpace _root_.Submission.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis


theorem continuous_laplacian_complex {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Laplacian.laplacian f) := by
  have he : Laplacian.laplacian f = fun z => fderiv ℝ (fderiv ℝ f) z 1 1 +
      fderiv ℝ (fderiv ℝ f) z Complex.I Complex.I :=
    funext (laplacian_complex_eq_fderiv f)
  rw [he]
  have h := (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  exact ((h.clm_apply continuous_const).clm_apply continuous_const).add
    ((h.clm_apply continuous_const).clm_apply continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.continuous_laplacian_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.continuous_laplacian_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.continuous_laplacian_complex ``Submission.DifferentialGeometry.Analysis.continuous_laplacian_complex


theorem integrable_log_norm_mul_laplacian {f : ℂ → ℝ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) :
    Integrable (fun z => Real.log ‖z‖ * Laplacian.laplacian f z) := by
  exact locallyIntegrable_log_norm_complex.integrable_smul_right_of_hasCompactSupport
    (continuous_laplacian_complex hf)
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset f))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_log_norm_mul_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_log_norm_mul_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_log_norm_mul_laplacian ``Submission.DifferentialGeometry.Analysis.integrable_log_norm_mul_laplacian

private theorem continuous_angular_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} (hf : Continuous f) :
    Continuous (fun r : ℝ => ∫ θ in -Real.pi..Real.pi, f (r, θ)) := by
  have h := continuous_parametric_integral_of_continuous
    (μ := (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℝ)) (f := fun r θ => f (r, θ)) (by convert! hf)
    (_root_.CompactIccSpace.isCompact_Icc : IsCompact (_root_.Set.Icc (-Real.pi) Real.pi))
  have he (r : ℝ) : (∫ θ in -Real.pi..Real.pi, f (r, θ)) =
      ∫ θ in _root_.Set.Icc (-Real.pi) Real.pi, f (r, θ) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact _root_.MeasureTheory.setIntegral_congr_set (_root_.MeasureTheory.Ioc_ae_eq_Icc (α := ℝ) (μ := _root_.MeasureTheory.MeasureSpace.volume))
  simp_rw [he]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.continuous_angular_integral
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.continuous_angular_integral target :: scope.openDecls } }


theorem tendsto_polar_circle_integral_zero {f : ℂ → ℝ} (hf : Continuous f) :
    _root_.Filter.Tendsto (fun r : ℝ => ∫ θ in -Real.pi..Real.pi, f (Complex.polarCoord.symm (r, θ)))
      (𝓝 0) (𝓝 ((2 * Real.pi) * f 0)) := by
  have hcont : Continuous (fun p : ℝ × ℝ => f (Complex.polarCoord.symm p)) := by
    apply hf.comp
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_polarCoord_symm
  have h := (continuous_angular_integral hcont).tendsto 0
  simpa [two_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_polar_circle_integral_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_polar_circle_integral_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_polar_circle_integral_zero ``Submission.DifferentialGeometry.Analysis.tendsto_polar_circle_integral_zero



theorem tendsto_log_polar_test_derivative_zero {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    _root_.Filter.Tendsto (fun r : ℝ => r * Real.log r *
      ∫ θ in -Real.pi..Real.pi,
        fderiv ℝ f (Complex.polarCoord.symm (r, θ))
          (Complex.polarCoord.symm (1, θ))) (𝓝 0) (𝓝 0) := by
  have hp : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hunit : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm (1, p.2)) :=
    hp.comp (continuous_const.prodMk continuous_snd)
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hjoint := (hdf.comp hp).clm_apply hunit
  have hlim := (continuous_angular_integral hjoint).tendsto 0
  simpa only [_root_.MulZeroClass.zero_mul, Function.comp_apply] using! tendsto_self_mul_log_nhds_zero.mul hlim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_log_polar_test_derivative_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_log_polar_test_derivative_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_log_polar_test_derivative_zero ``Submission.DifferentialGeometry.Analysis.tendsto_log_polar_test_derivative_zero



theorem tendsto_integral_annulus_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → E} {R : ℝ}
    (hf : _root_.MeasureTheory.IntegrableOn f {z : ℂ | ‖z‖ ≤ R}) :
    _root_.Filter.Tendsto (fun r : ℝ => ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, f z)
      (𝓝 0) (𝓝 (∫ z in {z : ℂ | ‖z‖ ≤ R}, f z)) := by
  let μ := volume.restrict {z : ℂ | ‖z‖ ≤ R}
  let A (r : ℝ) : Set ℂ := {z | r ≤ ‖z‖}
  have hm (r : ℝ) : MeasurableSet (A r) := measurableSet_le measurable_const measurable_norm
  have hlim : ∀ᵐ z ∂μ, _root_.Filter.Tendsto (fun r : ℝ => (A r).indicator f z) (𝓝 0) (𝓝 (f z)) := by
    have hz : ∀ᵐ z : ℂ ∂μ, z ≠ 0 := by
      apply _root_.MeasureTheory.ae_restrict_of_ae
      simp [_root_.MeasureTheory.ae_iff]
    filter_upwards [hz] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_nhds (norm_pos_iff.mpr hz)] with r hr
    exact (_root_.Set.indicator_of_mem (show z ∈ A r from hr.le) f).symm
  have h := _root_.MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun z => ‖f z‖)
    (Eventually.of_forall fun r => hf.aestronglyMeasurable.indicator (hm r))
    (Eventually.of_forall fun r => Eventually.of_forall fun z => norm_indicator_le_norm_self f z)
    hf.norm hlim
  have he (r : ℝ) : (∫ z, (A r).indicator f z ∂μ) =
      ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, f z := by
    rw [show μ = volume.restrict {z : ℂ | ‖z‖ ≤ R} from rfl, _root_.MeasureTheory.setIntegral_indicator (hm r)]
    have hs : {z : ℂ | ‖z‖ ≤ R} ∩ A r = {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R} := by
      ext z
      simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_ofPred_eq, A, _root_.Set.mem_Icc, and_comm]
    rw [hs]
  simpa only [he] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_annulus_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_annulus_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_annulus_zero ``Submission.DifferentialGeometry.Analysis.tendsto_integral_annulus_zero


theorem polar_point_eq_smul_unit (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = r • Complex.polarCoord.symm (1, θ) := by
  simp [Complex.polarCoord_symm_apply, Complex.real_smul, mul_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.polar_point_eq_smul_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.polar_point_eq_smul_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.polar_point_eq_smul_unit ``Submission.DifferentialGeometry.Analysis.polar_point_eq_smul_unit



theorem fderiv_log_norm_polar_unit {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    fderiv ℝ (fun z : ℂ => Real.log ‖z‖) (Complex.polarCoord.symm (r, θ))
      (Complex.polarCoord.symm (1, θ)) = r⁻¹ := by
  have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
  have hz : Complex.polarCoord.symm (r, θ) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn]
    exact hr.ne'
  rw [(hasFDerivAt_log_norm_complex hz).fderiv]
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul,
    polar_point_eq_smul_unit r θ, real_inner_smul_left, real_inner_self_eq_norm_sq,
    Complex.norm_polarCoord_symm, abs_one, one_pow, mul_one, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr]
  field_simp [hr.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.fderiv_log_norm_polar_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.fderiv_log_norm_polar_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.fderiv_log_norm_polar_unit ``Submission.DifferentialGeometry.Analysis.fderiv_log_norm_polar_unit


theorem greenRadialFlux_log (f : ℂ → ℝ) {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f r θ =
      r * Real.log r * fderiv ℝ f (Complex.polarCoord.symm (r, θ))
        (Complex.polarCoord.symm (1, θ)) - f (Complex.polarCoord.symm (r, θ)) := by
  simp only [greenRadialFlux, Complex.norm_polarCoord_symm, abs_of_pos hr,
    fderiv_log_norm_polar_unit hr]
  field_simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.greenRadialFlux_log then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.greenRadialFlux_log"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.greenRadialFlux_log ``Submission.DifferentialGeometry.Analysis.greenRadialFlux_log


theorem integral_log_laplacian_annulus {f : ℂ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hf : ∀ z, ‖z‖ ∈ _root_.Set.Icc r R → ContDiffAt ℝ 2 f z) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, Real.log ‖z‖ * Laplacian.laplacian f z) =
      (∫ θ in -Real.pi..Real.pi, greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f R θ) -
        ∫ θ in -Real.pi..Real.pi, greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f r θ := by
  have hz (z : ℂ) (h : ‖z‖ ∈ _root_.Set.Icc r R) : z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (hr.trans_le h.1))
  have hlog z h : ContDiffAt ℝ 2 (fun z : ℂ => Real.log ‖z‖) z :=
    (contDiffAt_id.norm ℝ (hz z h)).log (norm_ne_zero_iff.mpr (hz z h))
  rw [← integral_green_annulus hr hrR hlog hf]
  apply _root_.MeasureTheory.setIntegral_congr_fun (measurableSet_Icc.preimage continuous_norm.measurable)
  intro z h
  simp only [laplacian_log_norm_complex (hz z h), _root_.MulZeroClass.mul_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_log_laplacian_annulus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_log_laplacian_annulus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_log_laplacian_annulus ``Submission.DifferentialGeometry.Analysis.integral_log_laplacian_annulus



theorem tendsto_integral_greenRadialFlux_log_zero {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    _root_.Filter.Tendsto (fun r : ℝ => ∫ θ in -Real.pi..Real.pi,
      greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f r θ)
      (𝓝[>] 0) (𝓝 (-((2 * Real.pi) * f 0))) := by
  have h := (tendsto_log_polar_test_derivative_zero hf).sub
    (tendsto_polar_circle_integral_zero hf.continuous)
  simp only [zero_sub] at h
  apply (h.mono_left inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : Continuous (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have he : Continuous (fun θ : ℝ => Complex.polarCoord.symm (1, θ)) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hd := ((hf.continuous_fderiv (by norm_num)).comp hp).clm_apply he
  simp_rw [greenRadialFlux_log f hr]
  erw [intervalIntegral.integral_sub
    ((continuous_const.mul hd).intervalIntegrable _ _)
    ((hf.continuous.comp hp).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_greenRadialFlux_log_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_greenRadialFlux_log_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_greenRadialFlux_log_zero ``Submission.DifferentialGeometry.Analysis.tendsto_integral_greenRadialFlux_log_zero




theorem integral_log_norm_mul_laplacian {f : ℂ → ℝ}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 2 f) :
    (∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian f z) = (2 * Real.pi) * f 0 := by
  obtain ⟨R, hR, hs⟩ := hc.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hout (z : ℂ) (hz : R ≤ ‖z‖) : z ∉ tsupport f := by
    intro h
    have hlt : ‖z‖ < R := by simpa only [mem_ball_zero_iff] using hs h
    exact (not_lt_of_ge hz) hlt
  have hedge (θ : ℝ) : greenRadialFlux (fun z : ℂ => Real.log ‖z‖) f R θ = 0 := by
    have hz : Complex.polarCoord.symm (R, θ) ∉ tsupport f :=
      hout _ (by rw [Complex.norm_polarCoord_symm, abs_of_pos hR])
    simp only [greenRadialFlux]
    rw [fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
    simp
  have hi := integrable_log_norm_mul_laplacian hc hf
  have heq : (∫ z in {z : ℂ | ‖z‖ ≤ R}, Real.log ‖z‖ * Laplacian.laplacian f z) =
      ∫ z : ℂ, Real.log ‖z‖ * Laplacian.laplacian f z := by
    apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : z ∉ tsupport (Laplacian.laplacian f) :=
      fun h => hout z (le_of_not_ge hz) (tsupport_laplacian_subset f h)
    rw [image_eq_zero_of_notMem_tsupport hn, _root_.MulZeroClass.mul_zero]
  have hlim := (tendsto_integral_annulus_zero (R := R) hi.integrableOn).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  rw [heq] at hlim
  have hflux := (tendsto_integral_greenRadialFlux_log_zero hf).neg
  simp only [neg_neg] at hflux
  have hgreen : _root_.Filter.Tendsto (fun r : ℝ => ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R},
      Real.log ‖z‖ * Laplacian.laplacian f z) (𝓝[>] 0) (𝓝 ((2 * Real.pi) * f 0)) := by
    apply hflux.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hR).filter_mono inf_le_left] with r hr hrR
    rw [integral_log_laplacian_annulus hr hrR.le (fun z _ => hf.contDiffAt)]
    simp only [hedge, intervalIntegral.integral_zero, zero_sub]
  exact tendsto_nhds_unique hlim hgreen

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_log_norm_mul_laplacian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_log_norm_mul_laplacian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_log_norm_mul_laplacian ``Submission.DifferentialGeometry.Analysis.integral_log_norm_mul_laplacian

end DifferentialGeometry.Analysis
