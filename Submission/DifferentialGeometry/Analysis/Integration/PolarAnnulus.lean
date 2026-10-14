import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Polar.Complex
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.CircleIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis



theorem integral_annulus_eq_polar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, f z) =
      ∫ p in _root_.Set.Icc (r, -Real.pi) (R, Real.pi),
        p.1 • f (Complex.polarCoord.symm p) := by
  let A : Set ℂ := {z | ‖z‖ ∈ _root_.Set.Icc r R}
  let B : Set (ℝ × ℝ) := _root_.Set.Icc r R ×ˢ (_root_.Set.univ : Set ℝ)
  have hA : MeasurableSet A := measurableSet_Icc.preimage continuous_norm.measurable
  have hB : MeasurableSet B := measurableSet_Icc.prod MeasurableSet.univ
  rw [← _root_.MeasureTheory.integral_indicator hA, ← Complex.integral_comp_polarCoord_symm]
  have heq : (∫ p in polarCoord.target, p.1 • A.indicator f (Complex.polarCoord.symm p)) =
      ∫ p in polarCoord.target, B.indicator
        (fun p => p.1 • f (Complex.polarCoord.symm p)) p := by
    apply _root_.MeasureTheory.setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    have hp₀ : 0 < p.1 := hp.1
    have he : Complex.polarCoord.symm p ∈ A ↔ p ∈ B := by
      simp [A, B, abs_of_pos hp₀]
    by_cases h : p ∈ B
    · simp only [_root_.Set.indicator_of_mem (he.mpr h), _root_.Set.indicator_of_mem h]
    · simp only [_root_.Set.indicator_of_notMem (mt he.mp h), _root_.Set.indicator_of_notMem h, smul_zero]
  rw [heq, _root_.MeasureTheory.setIntegral_indicator hB]
  have hset : polarCoord.target ∩ B = _root_.Set.Icc r R ×ˢ _root_.Set.Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [polarCoord_target, B, _root_.Set.mem_inter_iff, _root_.Set.mem_prod, _root_.Set.mem_Ioi, _root_.Set.mem_Icc,
      _root_.Set.mem_univ, and_true, _root_.Set.mem_Ioo]
    constructor
    · rintro ⟨⟨_, hθ⟩, hp⟩
      exact ⟨hp, hθ⟩
    · rintro ⟨hp, hθ⟩
      exact ⟨⟨hr.trans_le hp.1, hθ⟩, hp⟩
  rw [hset, ← _root_.Set.Icc_prod_Icc]
  apply _root_.MeasureTheory.setIntegral_congr_set
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    (_root_.MeasureTheory.Ioo_ae_eq_Icc (α := ℝ) (μ := _root_.MeasureTheory.MeasureSpace.volume))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_eq_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_eq_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_eq_polar ``Submission.DifferentialGeometry.Analysis.integral_annulus_eq_polar

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

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

theorem integral_annulus_eq_integral_normalized_polar
    (f : ℂ → ℝ) {r R : ℝ} (hr : 0 < r)
    (hraw : _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      (_root_.Set.Icc r R ×ˢ _root_.Set.Icc (-Real.pi) Real.pi))
    (hnorm : _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)))
      (_root_.Set.Icc r R ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, f z) =
      (2 * Real.pi) * ∫ p in _root_.Set.Icc r R ×ˢ _root_.Set.Icc (0 : ℝ) 1,
        p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  rw [integral_annulus_eq_polar f hr]
  simp only [smul_eq_mul]
  rw [← _root_.Set.Icc_prod_Icc]
  rw [Measure.volume_eq_prod] at ⊢ hraw hnorm
  rw [_root_.MeasureTheory.setIntegral_prod _ hraw, _root_.MeasureTheory.setIntegral_prod _ hnorm]
  simp_rw [_root_.MeasureTheory.integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← _root_.MeasureTheory.integral_const_mul]
  congr 1
  funext ρ
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar ``Submission.DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar

private theorem integrableOn_mul_comp_polarCoord_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {r R B : ℝ} (hr : 0 < r)
    (hbound : ∀ z, ‖z‖ ∈ _root_.Set.Icc r R → ‖f z‖ ≤ B)
    {s : Set ℝ} (hs : IsCompact s) (θ : ℝ × ℝ → ℝ) (hθ : Measurable θ) :
    _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm (p.1, θ p)))
      (_root_.Set.Icc r R ×ˢ s) := by
  have hp : Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm (p.1, θ p)) := by
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hm : Measurable (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm (p.1, θ p))) :=
    measurable_fst.mul (hf.comp hp)
  apply IntegrableOn.of_bound ((isCompact_Icc.prod hs).measure_lt_top)
    hm.aestronglyMeasurable (|R| * _root_.Max.max B 0)
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod hs.measurableSet)] with p hp
  have hρ : 0 ≤ p.1 := hr.le.trans hp.1.1
  have hz : ‖Complex.polarCoord.symm (p.1, θ p)‖ ∈ _root_.Set.Icc r R := by
    simpa only [Complex.norm_polarCoord_symm, abs_of_nonneg hρ] using hp.1
  have hρR : ‖p.1‖ ≤ |R| := by
    rw [Real.norm_eq_abs, abs_of_nonneg hρ]
    exact hp.1.2.trans (le_abs_self R)
  rw [norm_mul]
  exact mul_le_mul hρR ((hbound _ hz).trans (le_max_left B 0)) (norm_nonneg _) (abs_nonneg R)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_mul_comp_polarCoord_of_bounded
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_mul_comp_polarCoord_of_bounded target :: scope.openDecls } }

theorem integrableOn_mul_comp_normalized_polar_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {r R B : ℝ} (hr : 0 < r)
    (hbound : ∀ z, ‖z‖ ∈ _root_.Set.Icc r R → ‖f z‖ ≤ B) :
    _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)))
      (_root_.Set.Icc r R ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
  integrableOn_mul_comp_polarCoord_of_bounded hf hr hbound _root_.CompactIccSpace.isCompact_Icc _ (by fun_prop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrableOn_mul_comp_normalized_polar_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrableOn_mul_comp_normalized_polar_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrableOn_mul_comp_normalized_polar_of_bounded ``Submission.DifferentialGeometry.Analysis.integrableOn_mul_comp_normalized_polar_of_bounded

theorem integral_annulus_eq_integral_normalized_polar_of_bounded
    {f : ℂ → ℝ} (hf : Measurable f) {r R B : ℝ} (hr : 0 < r)
    (hbound : ∀ z, ‖z‖ ∈ _root_.Set.Icc r R → ‖f z‖ ≤ B) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, f z) =
      (2 * Real.pi) * ∫ p in _root_.Set.Icc r R ×ˢ _root_.Set.Icc (0 : ℝ) 1,
        p.1 * f (Complex.polarCoord.symm (p.1, 2 * Real.pi * p.2 - Real.pi)) := by
  apply integral_annulus_eq_integral_normalized_polar f hr
  · exact integrableOn_mul_comp_polarCoord_of_bounded hf hr hbound _root_.CompactIccSpace.isCompact_Icc
      Prod.snd measurable_snd
  · exact integrableOn_mul_comp_normalized_polar_of_bounded hf hr hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar_of_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar_of_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar_of_bounded ``Submission.DifferentialGeometry.Analysis.integral_annulus_eq_integral_normalized_polar_of_bounded

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Analysis

private theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.polarCoord_symm_eq_circleMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.polarCoord_symm_eq_circleMap target :: scope.openDecls } }


private theorem continuous_circle_parameter :
    Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)) := by
  unfold circleMap
  fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.continuous_circle_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.continuous_circle_parameter target :: scope.openDecls } }

private theorem integrableOn_circle_parameter (g : ℂ → ℝ) (hg : Continuous g)
    (r R : ℝ) :
    _root_.MeasureTheory.Integrable (fun p : ℝ × ℝ => g (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi)))
      ((volume.restrict (_root_.Set.Icc r R)).prod (volume.restrict (_root_.Set.Icc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact (hg.comp continuous_circle_parameter).continuousOn.integrableOn_compact
    (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_circle_parameter
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_circle_parameter target :: scope.openDecls } }

theorem integrableOn_integral_circleMap (g : ℂ → ℝ) (hg : Continuous g) (r R : ℝ) :
    _root_.MeasureTheory.IntegrableOn (fun ρ => ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      g (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) (_root_.Set.Icc r R) :=
  (integrableOn_circle_parameter g hg r R).integral_prod_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrableOn_integral_circleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrableOn_integral_circleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrableOn_integral_circleMap ``Submission.DifferentialGeometry.Analysis.integrableOn_integral_circleMap

theorem integral_annulus_eq_integral_circleMap (g : ℂ → ℝ) (hg : Continuous g)
    {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, g z) =
      (2 * Real.pi) * ∫ ρ in _root_.Set.Icc r R, ρ * ∫ t in _root_.Set.Icc (0 : ℝ) 1,
        g (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1 * g (circleMap 0 p.1 p.2)) := by
    apply continuous_fst.mul
    apply hg.comp
    unfold circleMap
    fun_prop
  have hi : _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.1 * g (circleMap 0 p.1 p.2))
      (_root_.Set.Icc r R ×ˢ _root_.Set.Icc (-Real.pi) Real.pi) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc)
  rw [integral_annulus_eq_polar g hr]
  simp_rw [polarCoord_symm_eq_circleMap, smul_eq_mul]
  rw [← _root_.Set.Icc_prod_Icc, Measure.volume_eq_prod, _root_.MeasureTheory.setIntegral_prod _ hi]
  simp_rw [_root_.MeasureTheory.integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← _root_.MeasureTheory.integral_const_mul]
  congr 1
  funext ρ
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_eq_integral_circleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_eq_integral_circleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_eq_integral_circleMap ``Submission.DifferentialGeometry.Analysis.integral_annulus_eq_integral_circleMap

theorem integral_circleMap_norm_sq_radial_le
    {F : Type*} [SeminormedAddCommGroup F] {f : ℂ → F} (hf : Continuous f)
    {r R : ℝ} (hr : 0 < r) :
    (∫ ρ in _root_.Set.Icc r R, ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖f (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2) ≤
      (2 * Real.pi * r)⁻¹ * ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, ‖f z‖ ^ 2 := by
  let M : ℝ → ℝ := fun ρ => ∫ t in _root_.Set.Icc (0 : ℝ) 1,
    ‖f (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2
  have hM : _root_.MeasureTheory.IntegrableOn M (_root_.Set.Icc r R) :=
    integrableOn_integral_circleMap (fun z => ‖f z‖ ^ 2) (hf.norm.pow 2) r R
  have hρM : _root_.MeasureTheory.IntegrableOn (fun ρ => ρ * M ρ) (_root_.Set.Icc r R) := by
    have hc : Continuous (fun p : ℝ × ℝ => p.1 *
        ‖f (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi))‖ ^ 2) :=
      continuous_fst.mul ((hf.comp continuous_circle_parameter).norm.pow 2)
    have hi : _root_.MeasureTheory.Integrable (fun p : ℝ × ℝ => p.1 *
        ‖f (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi))‖ ^ 2)
        ((volume.restrict (_root_.Set.Icc r R)).prod (volume.restrict (_root_.Set.Icc (0 : ℝ) 1))) := by
      rw [Measure.prod_restrict]
      exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc)
    simpa only [_root_.MeasureTheory.IntegrableOn, _root_.MeasureTheory.integral_const_mul, M] using hi.integral_prod_left
  have hMnonneg (ρ : ℝ) : 0 ≤ M ρ := _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hle : r * (∫ ρ in _root_.Set.Icc r R, M ρ) ≤ ∫ ρ in _root_.Set.Icc r R, ρ * M ρ := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    exact _root_.MeasureTheory.setIntegral_mono_on (hM.const_mul r) hρM measurableSet_Icc
      (fun ρ hρ => mul_le_mul_of_nonneg_right hρ.1 (hMnonneg ρ))
  have heq := integral_annulus_eq_integral_circleMap (fun z => ‖f z‖ ^ 2) (hf.norm.pow 2) (R := R) hr
  change (∫ ρ in _root_.Set.Icc r R, M ρ) ≤ _
  rw [heq]
  have hpos : 0 < 2 * Real.pi * r := by positivity
  have hscaled :
      (2 * Real.pi * r) * (∫ ρ in _root_.Set.Icc r R, M ρ) ≤
        (2 * Real.pi * r) * ((2 * Real.pi * r)⁻¹ *
          ((2 * Real.pi) * ∫ ρ in _root_.Set.Icc r R, ρ * M ρ)) := by
    calc
      (2 * Real.pi * r) * (∫ ρ in _root_.Set.Icc r R, M ρ) =
          (2 * Real.pi) * (r * ∫ ρ in _root_.Set.Icc r R, M ρ) := by ring
      _ ≤ (2 * Real.pi) * ∫ ρ in _root_.Set.Icc r R, ρ * M ρ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_circleMap_norm_sq_radial_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_circleMap_norm_sq_radial_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_circleMap_norm_sq_radial_le ``Submission.DifferentialGeometry.Analysis.integral_circleMap_norm_sq_radial_le

theorem tendsto_integral_circleMap_norm_sq_radial_zero
    {F : Type*} [SeminormedAddCommGroup F] {f : ℕ → ℂ → F}
    (hf : ∀ n, Continuous (f n)) {r R : ℝ} (hr : 0 < r)
    (hlim : _root_.Filter.Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, ‖f n z‖ ^ 2)
      _root_.Filter.atTop (𝓝 0)) :
    _root_.Filter.Tendsto (fun n => ∫ ρ in _root_.Set.Icc r R, ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖f n (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2) _root_.Filter.atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => _root_.MeasureTheory.integral_nonneg fun _ => _root_.MeasureTheory.integral_nonneg fun _ => sq_nonneg _)
    (fun n => integral_circleMap_norm_sq_radial_le (hf n) hr)
  simpa only [_root_.MulZeroClass.mul_zero] using hlim.const_mul (2 * Real.pi * r)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_circleMap_norm_sq_radial_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_circleMap_norm_sq_radial_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_circleMap_norm_sq_radial_zero ``Submission.DifferentialGeometry.Analysis.tendsto_integral_circleMap_norm_sq_radial_zero

end DifferentialGeometry.Analysis

end

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Analysis




private theorem integral_annulus_eq_integral_circleMap_of_integrable
    (g : ℂ → ℝ) {r R : ℝ} (hr : 0 < r)
    (hi : _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.1 * g (circleMap 0 p.1 p.2))
      (_root_.Set.Icc r R ×ˢ _root_.Set.Icc (-Real.pi) Real.pi) (volume.prod _root_.MeasureTheory.MeasureSpace.volume)) :
    (∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, g z) =
      (2 * Real.pi) * ∫ ρ in _root_.Set.Icc r R, ρ * ∫ t in _root_.Set.Icc (0 : ℝ) 1,
        g (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) := by
  have hp (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]
  rw [integral_annulus_eq_polar g hr]
  simp_rw [hp, smul_eq_mul]
  rw [← _root_.Set.Icc_prod_Icc, Measure.volume_eq_prod, _root_.MeasureTheory.setIntegral_prod _ hi]
  simp_rw [_root_.MeasureTheory.integral_const_mul, integral_Icc_comp_circle_parameter]
  rw [← _root_.MeasureTheory.integral_const_mul]
  congr 1
  funext ρ
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integral_annulus_eq_integral_circleMap_of_integrable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integral_annulus_eq_integral_circleMap_of_integrable target :: scope.openDecls } }

private theorem norm_deriv_comp_circleMap_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : ℂ → F}
    {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ)
    (hu : DifferentiableAt ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) :
    ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ≤
      ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ * (2 * Real.pi * ρ) := by
  have hθ : HasDerivAt (fun t : ℝ => 2 * Real.pi * t - Real.pi) (2 * Real.pi) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * Real.pi)).sub_const Real.pi
  have hc := (hasDerivAt_circleMap 0 ρ (2 * Real.pi * t - Real.pi)).scomp t hθ
  have hchain := hu.hasFDerivAt.comp_hasDerivAt t hc
  rw [show deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t =
      fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))
        ((2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)) from
    hchain.deriv]
  calc
    _ ≤ ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ *
        ‖(2 * Real.pi) • (circleMap 0 ρ (2 * Real.pi * t - Real.pi) * Complex.I)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by
      simp [abs_of_nonneg hρ, abs_of_pos Real.pi_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.norm_deriv_comp_circleMap_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.norm_deriv_comp_circleMap_le target :: scope.openDecls } }

private theorem integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    _root_.MeasureTheory.IntegrableOn (fun ρ => ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) (_root_.Set.Icc r R) ∧
    (∫ ρ in _root_.Set.Icc r R, ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤
      (2 * Real.pi * R) * ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, ‖fderiv ℝ u z‖ ^ 2 := by
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc r R)
  let ν : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc (0 : ℝ) 1)
  let q : ℝ × ℝ → ℝ := fun p =>
    ‖deriv (fun t => u (circleMap 0 p.1 (2 * Real.pi * t - Real.pi))) p.2‖ ^ 2
  let b : ℝ × ℝ → ℝ := fun p => (2 * Real.pi) * p.1 *
    ‖fderiv ℝ u (circleMap 0 p.1 (2 * Real.pi * p.2 - Real.pi))‖ ^ 2
  have hR : 0 < R := hr.trans_le hrR
  have hqmeas : Measurable q :=
    (stronglyMeasurable_deriv_with_param
      (f := fun ρ t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi)))
      (hu.continuous.comp continuous_circle_parameter)).norm.measurable.pow_const 2
  have hbmeas : Measurable b := by
    apply Measurable.mul
    · exact measurable_const.mul measurable_fst
    · exact ((measurable_fderiv ℝ u).comp continuous_circle_parameter.measurable).norm.pow_const 2
  have hdiff : ∀ᵐ ρ ∂μ, ∀ᵐ t ∂ν,
      DifferentiableAt ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) :=
    ae_ae_comp_circleMap_normalized (hu.ae_differentiableAt (μ := _root_.MeasureTheory.MeasureSpace.volume)) hr
  have hqboundAA : ∀ᵐ ρ ∂μ, ∀ᵐ t ∂ν, ‖q (ρ, t)‖ ≤ ((C : ℝ) * (2 * Real.pi * R)) ^ 2 := by
    filter_upwards [hdiff, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with ρ hρ hρmem
    filter_upwards [hρ] with t ht
    have hρ0 : 0 ≤ ρ := hr.le.trans hρmem.1
    have hd := norm_deriv_comp_circleMap_le hρ0 t ht
    have hnorm := norm_fderiv_le_of_lipschitz ℝ (x₀ := circleMap 0 ρ
      (2 * Real.pi * t - Real.pi)) hu
    have hρR : 2 * Real.pi * ρ ≤ 2 * Real.pi * R := by nlinarith [Real.pi_pos, hρmem.2]
    have hle : ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ≤
        (C : ℝ) * (2 * Real.pi * R) :=
      hd.trans (mul_le_mul hnorm hρR (by positivity) C.coe_nonneg)
    simpa only [q, norm_pow, norm_norm] using
      pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hqbound : ∀ᵐ p ∂μ.prod ν, ‖q p‖ ≤ ((C : ℝ) * (2 * Real.pi * R)) ^ 2 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_le hqmeas.norm measurable_const)).mpr
      hqboundAA
  have hqi : _root_.MeasureTheory.Integrable q (μ.prod ν) :=
    Integrable.of_bound hqmeas.aestronglyMeasurable _ hqbound
  have hbi : _root_.MeasureTheory.Integrable b (μ.prod ν) := by
    apply Integrable.of_bound hbmeas.aestronglyMeasurable ((2 * Real.pi * R) * (C : ℝ) ^ 2)
    have hρae : ∀ᵐ p ∂μ.prod ν, p.1 ∈ _root_.Set.Icc r R :=
      Measure.quasiMeasurePreserving_fst.ae (_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc)
    filter_upwards [hρae] with p hp
    have hρ0 : 0 ≤ p.1 := hr.le.trans hp.1
    have hnorm := norm_fderiv_le_of_lipschitz ℝ (x₀ := circleMap 0 p.1
      (2 * Real.pi * p.2 - Real.pi)) hu
    have hρR : 2 * Real.pi * p.1 ≤ 2 * Real.pi * R := by nlinarith [Real.pi_pos, hp.2]
    dsimp only [b]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hρR (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (sq_nonneg _) (by positivity)
  have hleAA : ∀ᵐ ρ ∂μ, ∀ᵐ t ∂ν, q (ρ, t) ≤ (2 * Real.pi * R) * b (ρ, t) := by
    filter_upwards [hdiff, _root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with ρ hρ hρmem
    filter_upwards [hρ] with t ht
    have hρ0 : 0 ≤ ρ := hr.le.trans hρmem.1
    have hd := norm_deriv_comp_circleMap_le hρ0 t ht
    have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have hrad : ρ ^ 2 ≤ R * ρ := by nlinarith [hρmem.2]
    have hcoef : (2 * Real.pi * ρ) ^ 2 ≤ (2 * Real.pi * R) * (2 * Real.pi * ρ) := by
      nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi)) (sub_nonneg.mpr hrad)]
    calc
      q (ρ, t) ≤ ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2 *
          (2 * Real.pi * ρ) ^ 2 := by simpa only [q, mul_pow] using hs
      _ ≤ ‖fderiv ℝ u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))‖ ^ 2 *
          ((2 * Real.pi * R) * (2 * Real.pi * ρ)) :=
        mul_le_mul_of_nonneg_left hcoef (sq_nonneg _)
      _ = _ := by dsimp [b]; ring
  have hleE : ∀ᵐ ρ ∂μ, (∫ t, q (ρ, t) ∂ν) ≤ (2 * Real.pi * R) * ∫ t, b (ρ, t) ∂ν := by
    filter_upwards [hqi.prod_right_ae, hbi.prod_right_ae, hleAA] with ρ hqρ hbρ hle
    simpa only [_root_.MeasureTheory.integral_const_mul] using _root_.MeasureTheory.integral_mono_ae hqρ (hbρ.const_mul (2 * Real.pi * R)) hle
  have hiPolar : _root_.MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖fderiv ℝ u (circleMap 0 p.1 p.2)‖ ^ 2)
      (_root_.Set.Icc r R ×ˢ _root_.Set.Icc (-Real.pi) Real.pi) (volume.prod _root_.MeasureTheory.MeasureSpace.volume) := by
    have hcir : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
      unfold circleMap
      fun_prop
    have hm : Measurable (fun p : ℝ × ℝ => p.1 * ‖fderiv ℝ u (circleMap 0 p.1 p.2)‖ ^ 2) :=
      measurable_fst.mul (((measurable_fderiv ℝ u).comp hcir.measurable).norm.pow_const 2)
    apply IntegrableOn.of_bound
      ((isCompact_Icc.prod _root_.CompactIccSpace.isCompact_Icc).measure_lt_top) hm.aestronglyMeasurable
      (R * (C : ℝ) ^ 2)
    filter_upwards [_root_.MeasureTheory.ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hρ0 : 0 ≤ p.1 := hr.le.trans hp.1.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hp.1.2
      (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hu) 2)
      (sq_nonneg _) hR.le
  have heq := integral_annulus_eq_integral_circleMap_of_integrable
    (fun z => ‖fderiv ℝ u z‖ ^ 2) hr hiPolar
  have hbint : (∫ ρ, ∫ t, b (ρ, t) ∂ν ∂μ) =
      ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, ‖fderiv ℝ u z‖ ^ 2 := by
    rw [heq]
    dsimp only [b, μ, ν]
    simp_rw [_root_.MeasureTheory.integral_const_mul]
    rw [← _root_.MeasureTheory.integral_const_mul]
    congr 1
    funext ρ
    ring
  refine ⟨hqi.integral_prod_left, ?_⟩
  have h := _root_.MeasureTheory.integral_mono_ae hqi.integral_prod_left
    (hbi.integral_prod_left.const_mul (2 * Real.pi * R)) hleE
  rw [_root_.MeasureTheory.integral_const_mul, hbint] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le target :: scope.openDecls } }

theorem integrableOn_integral_norm_sq_deriv_circleMap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    _root_.MeasureTheory.IntegrableOn (fun ρ => ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) (_root_.Set.Icc r R) :=
  (integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le hu hr hrR).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrableOn_integral_norm_sq_deriv_circleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrableOn_integral_norm_sq_deriv_circleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrableOn_integral_norm_sq_deriv_circleMap ``Submission.DifferentialGeometry.Analysis.integrableOn_integral_norm_sq_deriv_circleMap

theorem integral_norm_sq_deriv_circleMap_radial_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u : ℂ → F} {C : ℝ≥0} (hu : LipschitzWith C u) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    (∫ ρ in _root_.Set.Icc r R, ∫ t in _root_.Set.Icc (0 : ℝ) 1,
      ‖deriv (fun t => u (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) t‖ ^ 2) ≤
      (2 * Real.pi * R) * ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, ‖fderiv ℝ u z‖ ^ 2 :=
  (integrableOn_and_integral_norm_sq_deriv_circleMap_radial_le hu hr hrR).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_norm_sq_deriv_circleMap_radial_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_norm_sq_deriv_circleMap_radial_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_norm_sq_deriv_circleMap_radial_le ``Submission.DifferentialGeometry.Analysis.integral_norm_sq_deriv_circleMap_radial_le

end DifferentialGeometry.Analysis

end
