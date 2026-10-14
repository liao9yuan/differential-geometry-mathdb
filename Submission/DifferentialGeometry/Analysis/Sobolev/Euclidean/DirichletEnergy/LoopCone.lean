import Submission.DifferentialGeometry.Analysis.Calculus.Interpolation.RadialCone
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Polar
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.NNReal _root_.ENNReal _root_.Topology

namespace DifferentialGeometry.Analysis

private theorem integral_Icc_comp_circle_parameter (g : ℝ → ℝ) :
    (∫ θ in _root_.Set.Icc (-Real.pi) Real.pi, g θ) =
      (2 * Real.pi) * ∫ t in _root_.Set.Icc (0 : ℝ) 1, g (2 * Real.pi * t - Real.pi) := by
  have h := intervalIntegral.smul_integral_comp_mul_sub (a := 0) (b := 1)
    g (2 * Real.pi) Real.pi
  have hπ : 2 * Real.pi * 1 - Real.pi = Real.pi := by ring
  simp only [_root_.MulZeroClass.mul_zero, zero_sub, hπ, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc, ← _root_.MeasureTheory.integral_Icc_eq_integral_Ioc] at h
  exact h.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_Icc_comp_circle_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_Icc_comp_circle_parameter target :: scope.openDecls } }

private theorem integral_unitDisk_eq_polar (f : ℂ → ℝ) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, f z) =
      ∫ p in _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (-Real.pi) Real.pi, p.1 * f (Complex.polarCoord.symm p) := by
  let A := Metric.closedBall (0 : ℂ) 1
  let B : Set (ℝ × ℝ) := _root_.Set.Icc (0 : ℝ) 1 ×ˢ (_root_.Set.univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_closedBall
  have hB : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  rw [← _root_.MeasureTheory.integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, B.indicator
        (fun p => p.1 * f (Complex.polarCoord.symm p)) p := by
    apply _root_.MeasureTheory.setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    have hmem : Complex.polarCoord.symm p ∈ A ↔ p ∈ B := by
      simp [A, B, abs_of_pos hp0, hp0.le]
    by_cases h : p ∈ B
    · simp only [_root_.Set.indicator_of_mem (hmem.mpr h), _root_.Set.indicator_of_mem h, smul_eq_mul]
    · simp only [_root_.Set.indicator_of_notMem (mt hmem.mp h), _root_.Set.indicator_of_notMem h, smul_zero]
  rw [heq, _root_.MeasureTheory.setIntegral_indicator hB]
  have hset : polarCoord.target ∩ B = _root_.Set.Ioc (0 : ℝ) 1 ×ˢ _root_.Set.Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target, B, _root_.Set.mem_inter_iff, _root_.Set.mem_prod, _root_.Set.mem_Ioi, _root_.Set.mem_Icc,
      _root_.Set.mem_univ, and_true, _root_.Set.mem_Ioo, _root_.Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hp, hθ⟩, hρ⟩
      exact ⟨⟨hp, hρ.2⟩, hθ⟩
    · rintro ⟨hρ, hθ⟩
      exact ⟨⟨hρ.1, hθ⟩, hρ.1.le, hρ.2⟩
  rw [hset]
  exact _root_.MeasureTheory.setIntegral_congr_set (Measure.set_prod_ae_eq _root_.MeasureTheory.Ioc_ae_eq_Icc _root_.MeasureTheory.Ioo_ae_eq_Icc)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_unitDisk_eq_polar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_unitDisk_eq_polar target :: scope.openDecls } }

private theorem integral_unitDisk_eq_normalized_polar_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {B : ℝ}
    (hbound : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖f z‖ ≤ B) :
    (∫ z in Metric.closedBall (0 : ℂ) 1, f z) =
      (2 * Real.pi) * ∫ p in _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (0 : ℝ) 1,
        p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  have hi {s : Set ℝ} (hs : IsCompact s) (θ : ℝ × ℝ → ℝ) (hθ : Measurable θ) :
      _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm (p.1, θ p)))
        (_root_.Set.Icc (0 : ℝ) 1 ×ˢ s) := by
    have hp : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm (p.1, θ p)) := by
      simp only [Complex.polarCoord_symm_apply]
      fun_prop
    have hm := measurable_fst.mul (hf.comp hp)
    apply IntegrableOn.of_bound ((isCompact_Icc.prod hs).measure_lt_top)
      hm.aestronglyMeasurable (_root_.Max.max B 0)
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod hs.measurableSet)] with p hp
    have hn : ‖Complex.polarCoord.symm (p.1, θ p)‖ ≤ 1 := by
      simpa only [Complex.norm_polarCoord_symm, abs_of_nonneg hp.1.1] using hp.1.2
    change ‖p.1 * f (Complex.polarCoord.symm (p.1, θ p))‖ ≤ _root_.Max.max B 0
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hp.1.1]
    exact (mul_le_mul hp.1.2 (hbound _ (Metric.mem_closedBall.mpr
      (by simpa only [dist_zero_right] using hn))) (norm_nonneg _) zero_le_one).trans
        (by simp)
  rw [integral_unitDisk_eq_polar]
  have hraw := hi (s := _root_.Set.Icc (-Real.pi) Real.pi) _root_.CompactIccSpace.isCompact_Icc Prod.snd measurable_snd
  have hnorm := hi (s := _root_.Set.Icc (0 : ℝ) 1) _root_.CompactIccSpace.isCompact_Icc
    (fun p => 2 * Real.pi * p.2 - Real.pi) (by fun_prop)
  rw [Measure.volume_eq_prod] at ⊢ hraw hnorm
  rw [_root_.MeasureTheory.setIntegral_prod _ hraw, _root_.MeasureTheory.setIntegral_prod _ hnorm]
  simp_rw [_root_.MeasureTheory.integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← _root_.MeasureTheory.integral_const_mul]
  congr 1
  funext ρ
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_unitDisk_eq_normalized_polar_of_bounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_unitDisk_eq_normalized_polar_of_bounded target :: scope.openDecls } }

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem integral_energy_periodicLoopCone_le
    (p : F) {a : ℝ → F} {K : ℝ≥0} (ha : Function.Periodic a 1) (hLip : LipschitzWith K a) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      (‖fderiv ℝ (periodicLoopCone p ha) z 1‖ ^ 2 +
        ‖fderiv ℝ (periodicLoopCone p ha) z Complex.I‖ ^ 2) / 2) ≤
      (Real.pi / 2) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a t - p‖ ^ 2) +
        (1 / (8 * Real.pi)) * (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2) := by
  borelize F
  let g := periodicLoopCone p ha
  let e (z : ℂ) := (‖fderiv ℝ g z 1‖ ^ 2 + ‖fderiv ℝ g z Complex.I‖ ^ 2) / 2
  let q (t : ℝ) := (‖a t - p‖ ^ 2 + ‖deriv a t‖ ^ 2 / (2 * Real.pi) ^ 2) / 2
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc (0 : ℝ) 1)
  obtain ⟨C, hC⟩ := exists_lipschitzWith_periodicLoopCone p ha hLip
  have hemeas : Measurable e :=
    (((measurable_fderiv_apply_const ℝ g 1).norm.pow_const 2).add
      ((measurable_fderiv_apply_const ℝ g Complex.I).norm.pow_const 2)).div_const 2
  have heb (z : ℂ) : ‖e z‖ ≤ (C : ℝ) ^ 2 := by
    have h₁ := (fderiv ℝ g z).le_opNorm (1 : ℂ)
    have h₂ := (fderiv ℝ g z).le_opNorm Complex.I
    rw [_root_.NormOneClass.norm_one, mul_one] at h₁
    rw [Complex.norm_I, mul_one] at h₂
    have hD := norm_fderiv_le_of_lipschitz ℝ hC (x₀ := z)
    have hs₁ := pow_le_pow_left₀ (norm_nonneg _) (h₁.trans hD) 2
    have hs₂ := pow_le_pow_left₀ (norm_nonneg _) (h₂.trans hD) 2
    rw [Real.norm_of_nonneg (by dsimp [e]; positivity)]
    dsimp [e]
    nlinarith
  have hval : _root_.MeasureTheory.Integrable (fun t => ‖a t - p‖ ^ 2) μ :=
    ((hLip.continuous.sub continuous_const).norm.pow 2).integrableOn_Icc
  have hdm : _root_.MeasureTheory.MemLp (deriv a) 2 μ :=
    MemLp.of_bound (measurable_deriv a).aestronglyMeasurable K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hLip)
  have hdv : _root_.MeasureTheory.Integrable (fun t => ‖deriv a t‖ ^ 2) μ := hdm.norm.integrable_sq
  have hqi : _root_.MeasureTheory.Integrable q μ := ((hval.add (hdv.div_const _)).div_const 2)
  have hradi : _root_.MeasureTheory.Integrable (fun t : ℝ => t) μ := continuous_id.integrableOn_Icc
  have hright : _root_.MeasureTheory.Integrable (fun z : ℝ × ℝ => z.1 * q z.2) (μ.prod μ) := hradi.mul_prod hqi
  let w (z : ℝ × ℝ) := z.1 * e
    (Complex.polarCoord.symm (z.1, 2 * Real.pi * z.2 - Real.pi))
  have hwmeas : Measurable w := by
    apply measurable_fst.mul
    apply hemeas.comp
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hw : _root_.MeasureTheory.Integrable w (μ.prod μ) := by
    apply Integrable.of_bound hwmeas.aestronglyMeasurable ((C : ℝ) ^ 2)
    have hx : ∀ᵐ z : ℝ × ℝ ∂μ.prod μ, z.1 ∈ _root_.Set.Icc (0 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc)
    filter_upwards [hx] with z hz
    dsimp only [w]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact (mul_le_mul hz.2 (heb _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hrad : ∀ᵐ z ∂μ.prod μ, 0 < z.1 := by
    apply Measure.quasiMeasurePreserving_fst.ae
    change ∀ᵐ t ∂volume.restrict (_root_.Set.Icc (0 : ℝ) 1), 0 < t
    rw [← _root_.MeasureTheory.restrict_Ioc_eq_restrict_Icc]
    exact (_root_.MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono fun t ht => ht.1
  have had : ∀ᵐ z ∂μ.prod μ, DifferentiableAt ℝ a z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (_root_.MeasureTheory.ae_restrict_of_ae hLip.ae_differentiableAt_real)
  have hbound : ∀ᵐ z ∂μ.prod μ, w z ≤ z.1 * q z.2 := by
    filter_upwards [hrad, had] with z hz hza
    have hp := normalized_polar_fderiv_energy_le g hz
    have hc := fderiv_periodicLoopCone_normalized_polar p ha hz hza
    rw [hc.1, hc.2, norm_smul, Real.norm_eq_abs, abs_of_pos hz, mul_pow] at hp
    change z.1 * e _ ≤ z.1 * q z.2
    dsimp only [e, q]
    convert hp using 1 <;> field_simp [hz.ne', Real.pi_ne_zero]
  have hineq := _root_.MeasureTheory.integral_mono_ae hw hright hbound
  have heq := integral_unitDisk_eq_normalized_polar_of_bounded hemeas (fun z _ => heb z)
  change (∫ z in Metric.closedBall (0 : ℂ) 1, e z) ≤ _
  rw [heq, Measure.volume_eq_prod, ← Measure.prod_restrict]
  apply (mul_le_mul_of_nonneg_left hineq (by positivity : 0 ≤ 2 * Real.pi)).trans_eq
  rw [_root_.MeasureTheory.integral_prod _ hright]
  simp_rw [_root_.MeasureTheory.integral_const_mul]
  rw [_root_.MeasureTheory.integral_mul_const]
  have hrint : (∫ t, t ∂μ) = 1 / 2 := by
    change (∫ t in _root_.Set.Icc (0 : ℝ) 1, t) = 1 / 2
    rw [_root_.MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      integral_id]
    norm_num
  rw [hrint]
  dsimp only [q]
  rw [_root_.MeasureTheory.integral_div, _root_.MeasureTheory.integral_add hval (hdv.div_const _), _root_.MeasureTheory.integral_div]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_energy_periodicLoopCone_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_energy_periodicLoopCone_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_energy_periodicLoopCone_le ``Submission.DifferentialGeometry.Analysis.integral_energy_periodicLoopCone_le

end DifferentialGeometry.Analysis

end
