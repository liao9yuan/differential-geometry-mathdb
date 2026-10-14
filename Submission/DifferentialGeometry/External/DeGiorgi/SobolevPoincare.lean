-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Submission.DifferentialGeometry.External.DeGiorgi.Poincare
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtension
import Submission.DifferentialGeometry.External.DeGiorgi.BallExtensionEstimates
import Submission.DifferentialGeometry.External.DeGiorgi.LpFunctionToolkit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Sobolev-Poincare On The Unit Ball

For `1 < p < d` and `u ∈ W^{1,p}(B₁)`, we prove:

  ‖u − ū‖_{L^{p*}(B₁)} ≤ C(d,p) ‖∇u‖_{L^p(B₁)}

where `p* = dp/(d − p)` is the Sobolev conjugate exponent and `ū` is the
mean value of `u` over the unit ball.

## Proof strategy

1. Mean subtraction: form `v = u − ū` in `W^{1,p}(B₁)` with the same gradient.
2. Extension: `unitBallExtension(v)` gives a compactly supported
   `W^{1,p}(ℝ^d)` function agreeing with `v` on `B₁`.
3. Whole-space Sobolev: apply GNS to the extension.
4. Restriction: restrict the `L^{p*}` norm back to `B₁`.
5. Gradient absorption: extension gradient bound + Poincare.
-/

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter
open scoped _root_.ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Constants -/

/-- Intermediate constant for the extension gradient bound. -/
private noncomputable def C_extensionGrad (d : ℕ) (p : ℝ) : ℝ≥0∞ :=
  1 + CUnitBallExtensionGrad d p * (ENNReal.ofReal (CPoincVal d) + 1)

run_cmd do
  let target := ``Submission.DeGiorgi.C_extensionGrad
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.C_extensionGrad target :: scope.openDecls } }

/-- The Sobolev-Poincare constant on the unit ball. -/
noncomputable def CSobolevPoincare (d : ℕ) [NeZero d] (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (CGns d p) * C_extensionGrad d p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.CSobolevPoincare then
    throwError "Refusing to shadow existing declaration DeGiorgi.CSobolevPoincare"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.CSobolevPoincare ``Submission.DeGiorgi.CSobolevPoincare

/-! ## Subtracting constants -/

/-- Subtracting a constant from a `W^{1,p}` witness on the unit ball preserves
membership and leaves the weak gradient unchanged. -/
noncomputable def memW1pWitnessSubConstUnitBall
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1))
    (c : ℝ) :
    MemW1pWitness (ENNReal.ofReal p) (fun x => u x - c) (Metric.ball (0 : E) 1) := by
  haveI : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (Metric.ball (0 : E) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.lt_top⟩
  refine
    { memLp := hw.memLp.sub (_root_.MeasureTheory.memLp_const c)
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := hw.weakGrad_component_memLp
      isWeakGrad := ?_ }
  intro i φ hφ hφ_supp hφ_sub
  let ei : E := EuclideanSpace.single i (1 : ℝ)
  have hkey := hw.isWeakGrad i φ hφ hφ_supp hφ_sub
  have hconst :
      HasWeakPartialDeriv i (fun _ : E => (0 : ℝ)) (fun _ : E => c)
        (Metric.ball (0 : E) 1) := by
    simpa [ei] using
      (HasWeakPartialDeriv.of_contDiff (Ω := Metric.ball (0 : E) 1) (i := i)
        (f := fun _ : E => c) _root_.Metric.isOpen_ball contDiff_const)
  have hconst_zero :
      ∫ x in Metric.ball (0 : E) 1, c * (fderiv ℝ φ x) ei = 0 := by
    simpa using hconst φ hφ hφ_supp hφ_sub
  have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
    (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) ei
  have hu_int : _root_.MeasureTheory.Integrable (fun x => u x * (fderiv ℝ φ x) ei)
      (volume.restrict (Metric.ball (0 : E) 1)) := by
    have hu_loc : _root_.MeasureTheory.LocallyIntegrable u (volume.restrict (Metric.ball (0 : E) 1)) :=
      hw.memLp.locallyIntegrable (by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal (le_of_lt hp))
    simpa [smul_eq_mul] using
      hu_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
  have hc_int : _root_.MeasureTheory.Integrable (fun x => c * (fderiv ℝ φ x) ei)
      (volume.restrict (Metric.ball (0 : E) 1)) :=
    (hderiv_cont.integrable_of_hasCompactSupport hderiv_supp).const_mul c
  have hsub_fun :
      (fun x => (u x - c) * (fderiv ℝ φ x) ei) =
        (fun x => u x * (fderiv ℝ φ x) ei - c * (fderiv ℝ φ x) ei) := by
    ext x
    ring
  rw [hsub_fun, _root_.MeasureTheory.integral_sub hu_int hc_int, hkey, hconst_zero]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.memW1pWitnessSubConstUnitBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.memW1pWitnessSubConstUnitBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.memW1pWitnessSubConstUnitBall ``Submission.DeGiorgi.memW1pWitnessSubConstUnitBall

/-- The weak gradient of the subtracted witness equals the original weak
gradient. -/
theorem memW1pWitness_sub_const_unitBall_weakGrad
    {p : ℝ} (hp : 1 < p) {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) (c : ℝ) :
    (memW1pWitnessSubConstUnitBall hp hw c).weakGrad = hw.weakGrad := by
  let _ := (inferInstance : NeZero d)
  simp [memW1pWitnessSubConstUnitBall]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.memW1pWitness_sub_const_unitBall_weakGrad then
    throwError "Refusing to shadow existing declaration DeGiorgi.memW1pWitness_sub_const_unitBall_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.memW1pWitness_sub_const_unitBall_weakGrad ``Submission.DeGiorgi.memW1pWitness_sub_const_unitBall_weakGrad

/-! ## Jensen for `eLpNorm` of averages -/

/-- **Jensen's inequality for `eLpNorm`**: the `L^p` norm of a constant equal to
the average is at most the `L^p` norm of the function.

For `1 ≤ p < ⊤`, an integrable `f`, and a finite measure `μ`:
  `eLpNorm (fun _ => ⨍ x, f x ∂μ) p μ ≤ eLpNorm f p μ`

This is a consequence of Jensen's inequality for the convex function `t ↦ |t|^p`,
proved here via Hölder's inequality (`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`)
combined with the norm bound for the Bochner integral average.

The proof avoids `EuclideanSpace` and works for any real-valued integrable function. -/
theorem eLpNorm_const_average_le
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} [_root_.MeasureTheory.IsFiniteMeasure μ]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : α → ℝ} (hf : _root_.MeasureTheory.Integrable f μ) :
    eLpNorm (fun _ => ⨍ x, f x ∂μ) p μ ≤ _root_.MeasureTheory.eLpNorm f p μ := by
  let _ := hp_top
  -- Trivial case: μ = 0
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp [_root_.MeasureTheory.eLpNorm_measure_zero]
  have hμ_ne : μ Set.univ ≠ 0 := by rwa [ne_eq, Measure.measure_univ_eq_zero]
  have hμ_top : μ Set.univ ≠ ⊤ := _root_.MeasureTheory.measure_ne_top μ _
  have hp_ne : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne'
  -- Proof: ‖⨍ f‖ ≤ (μ.real univ)⁻¹ * ‖∫ f‖ ≤ (μ.real univ)⁻¹ * (eLpNorm f 1 μ).toReal
  -- Then convert to ENNReal.
  have h_avg_enorm_le :
      ‖⨍ x, f x ∂μ‖ₑ ≤ (μ Set.univ)⁻¹ * _root_.MeasureTheory.eLpNorm f 1 μ := by
    have h_avg_bound : ‖⨍ x, f x ∂μ‖ ≤
        (μ.real Set.univ)⁻¹ * (_root_.MeasureTheory.eLpNorm f 1 μ).toReal := by
      simp only [_root_.MeasureTheory.average_eq]
      calc ‖(μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ‖
          ≤ ‖(μ.real Set.univ)⁻¹‖ * ‖∫ x, f x ∂μ‖ := norm_smul_le _ _
        _ = (μ.real Set.univ)⁻¹ * ‖∫ x, f x ∂μ‖ := by
            rw [Real.norm_of_nonneg (inv_nonneg.mpr _root_.MeasureTheory.measureReal_nonneg)]
        _ ≤ (μ.real Set.univ)⁻¹ * (_root_.MeasureTheory.eLpNorm f 1 μ).toReal := by
            gcongr
            calc ‖∫ x, f x ∂μ‖
                ≤ ∫ x, ‖f x‖ ∂μ := _root_.MeasureTheory.norm_integral_le_integral_norm _
              _ = (∫⁻ x, ‖f x‖ₑ ∂μ).toReal :=
                  _root_.MeasureTheory.integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable
              _ = (_root_.MeasureTheory.eLpNorm f 1 μ).toReal := by rw [_root_.MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    -- Convert ℝ bound to ENNReal
    have h_inv_eq : ENNReal.ofReal (μ.real Set.univ)⁻¹ = (μ Set.univ)⁻¹ := by
      rw [_root_.MeasureTheory.measureReal_def, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hμ_ne hμ_top),
        ENNReal.ofReal_toReal hμ_top]
    calc ‖⨍ x, f x ∂μ‖ₑ
        ≤ ENNReal.ofReal ((μ.real Set.univ)⁻¹ * (_root_.MeasureTheory.eLpNorm f 1 μ).toReal) := by
          simp only [Real.enorm_eq_ofReal_abs, ← Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal h_avg_bound
      _ = ENNReal.ofReal (μ.real Set.univ)⁻¹ * ENNReal.ofReal (_root_.MeasureTheory.eLpNorm f 1 μ).toReal :=
          ENNReal.ofReal_mul (inv_nonneg.mpr _root_.MeasureTheory.measureReal_nonneg)
      _ ≤ (μ Set.univ)⁻¹ * _root_.MeasureTheory.eLpNorm f 1 μ := by
          rw [h_inv_eq]; gcongr; exact ENNReal.ofReal_toReal_le
  set exp := 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal with hexp_def
  have h_holder : _root_.MeasureTheory.eLpNorm f 1 μ ≤
      eLpNorm f p μ * μ Set.univ ^ exp :=
    _root_.MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf.aestronglyMeasurable
  -- eLpNorm(const c) = ‖c‖ₑ * μ(univ)^{1/p}  [eLpNorm_const]
  -- ≤ (μ univ)⁻¹ * eLpNorm f p μ * μ(univ)^exp * μ(univ)^{1/p}
  -- = eLpNorm f p μ * ((μ univ)⁻¹ * μ(univ)^{exp + 1/p})
  -- Since exp + 1/p = 1/1 - 1/p + 1/p = 1: = eLpNorm f p μ * (μ univ)⁻¹ * μ univ = eLpNorm f p μ
  have hexp_simp : exp + 1 / p.toReal = 1 := by
    simp [hexp_def, show (1 : ℝ≥0∞).toReal = 1 from ENNReal.toReal_one]
  calc _root_.MeasureTheory.eLpNorm (fun _ => ⨍ x, f x ∂μ) p μ
      = ‖⨍ x, f x ∂μ‖ₑ * μ Set.univ ^ (1 / p.toReal) := _root_.MeasureTheory.eLpNorm_const _ hp_ne hμ
    _ ≤ ((μ Set.univ)⁻¹ * _root_.MeasureTheory.eLpNorm f 1 μ) * μ Set.univ ^ (1 / p.toReal) := by
        gcongr
    _ ≤ ((μ Set.univ)⁻¹ * (_root_.MeasureTheory.eLpNorm f p μ * μ Set.univ ^ exp)) *
          μ Set.univ ^ (1 / p.toReal) := by gcongr
    _ = _root_.MeasureTheory.eLpNorm f p μ * ((μ Set.univ)⁻¹ * (μ Set.univ ^ exp *
          μ Set.univ ^ (1 / p.toReal))) := by ring
    _ = _root_.MeasureTheory.eLpNorm f p μ * ((μ Set.univ)⁻¹ * μ Set.univ ^ (exp + 1 / p.toReal)) := by
        congr 2; exact (ENNReal.rpow_add exp (1 / p.toReal) hμ_ne hμ_top).symm
    _ = _root_.MeasureTheory.eLpNorm f p μ * ((μ Set.univ)⁻¹ * μ Set.univ ^ (1 : ℝ)) := by
        rw [hexp_simp]
    _ = _root_.MeasureTheory.eLpNorm f p μ * ((μ Set.univ)⁻¹ * μ Set.univ) := by
        rw [ENNReal.rpow_one]
    _ = _root_.MeasureTheory.eLpNorm f p μ := by rw [ENNReal.inv_mul_cancel hμ_ne hμ_top, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.eLpNorm_const_average_le then
    throwError "Refusing to shadow existing declaration DeGiorgi.eLpNorm_const_average_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.eLpNorm_const_average_le ``Submission.DeGiorgi.eLpNorm_const_average_le

/-! ## Poincare for `W^{1,p}` -/

/-- The ℓ² norm on `EuclideanSpace` is bounded by the ℓ¹ norm. -/
private lemma euclidean_norm_le_sum_norms (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ≤ ∑ i : Fin d, ‖v i‖ := by
  let _ := (inferInstance : NeZero d)
  rw [EuclideanSpace.norm_eq]
  let nv : Fin d → ℝ := fun i => ‖v i‖
  have hnv : ∀ i, 0 ≤ nv i := fun i => norm_nonneg (v i)
  change √(∑ i : Fin d, nv i ^ 2) ≤ ∑ i : Fin d, nv i
  calc √(∑ i : Fin d, nv i ^ 2)
      ≤ √((∑ i : Fin d, nv i) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [sq, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun j _ => hnv j) (Finset.mem_univ i)) (hnv i)
    _ = |∑ i : Fin d, nv i| := Real.sqrt_sq_eq_abs _
    _ = ∑ i : Fin d, nv i :=
        abs_of_nonneg (Finset.sum_nonneg fun i _ => hnv i)

run_cmd do
  let target := ``Submission.DeGiorgi.euclidean_norm_le_sum_norms
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.euclidean_norm_le_sum_norms target :: scope.openDecls } }

/-- Poincare inequality for `W^{1,p}` witnesses on the unit ball.
Proved by density of smooth functions + `ge_of_tendsto`. -/
private theorem poincare_unitBall_W1p
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
      (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) ≤
    ENNReal.ofReal (CPoincVal d) *
      _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  -- === Setup ===
  let B := Metric.ball (0 : E) 1
  let μ := volume.restrict B
  let pp := ENNReal.ofReal p
  let C := ENNReal.ofReal (CPoincVal d)
  have hp_pos : (0 : ℝ) < p := by linarith
  have hpp : (1 : ℝ≥0∞) ≤ pp := by
    simp only [pp]; rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hp)
  have hpp_top : pp ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ_fin : _root_.MeasureTheory.IsFiniteMeasure μ :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.lt_top⟩
  -- Measurability helpers
  have hu_aesm : _root_.MeasureTheory.AEStronglyMeasurable u μ := hw.memLp.aestronglyMeasurable
  have hG_comp_aesm : ∀ i : Fin d, _root_.MeasureTheory.AEStronglyMeasurable (fun x => hw.weakGrad x i) μ :=
    fun i => (hw.weakGrad_component_memLp i).aestronglyMeasurable
  -- === Trivial case: RHS = ⊤ ===
  by_cases h_top : C * _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ = ⊤
  · exact le_top.trans_eq h_top.symm
  -- === Smooth approximation ===
  obtain ⟨ψ, hψ_smooth, _, hψ_fn, hψ_grad⟩ :=
    exists_smooth_W1p_approx_on_unitBall (d := d) hp hw
  -- Smooth function measurability on μ
  have hψn_aesm : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (ψ n) μ :=
    fun n => (hψ_smooth n).continuous.aestronglyMeasurable.restrict
  have h_comp_aesm : ∀ n i, _root_.MeasureTheory.AEStronglyMeasurable
      (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) μ :=
    fun n i =>
      (((hψ_smooth n).continuous_fderiv
        (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const).aestronglyMeasurable.restrict.sub (hG_comp_aesm i)
  -- === Smooth Poincaré for each n ===
  have h_poinc : ∀ n,
      _root_.MeasureTheory.eLpNorm (fun x => ψ n x - ⨍ y in B, ψ n y ∂volume) pp μ ≤
        C * _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖) pp μ :=
    fun n => poincare_smooth_unitBall (d := d) (le_of_lt hp) (hψ_smooth n)
  -- === Gradient error → 0 ===
  -- Pointwise: ‖ ‖fderiv ψ_n x‖ - ‖hw.weakGrad x‖ ‖ ≤ ∑ᵢ ‖∂ᵢψ_n(x) - gᵢ(x)‖
  -- by norm_fderiv_eq_norm_partials_local + reverse triangle + euclidean_norm_le_sum_norms
  -- Then Minkowski (Finset induction on eLpNorm_add_le) gives the eLpNorm bound.
  have h_grad_err : ∀ n,
      _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖) pp μ ≤
        ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          pp μ := by
    intro n
    -- Pointwise: ‖ ‖fderiv ψ_n x‖ - ‖G x‖ ‖ ≤ ∑ᵢ ‖∂ᵢψ_n(x) - gᵢ(x)‖
    have h_ptwise : ∀ x : E, ‖‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖‖ ≤
        ∑ i : Fin d,
          ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖ := by
      intro x
      let vn : E := WithLp.toLp 2
        (fun i => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1))
      calc ‖‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖‖
          = |‖vn‖ - ‖hw.weakGrad x‖| := by
            rw [Real.norm_eq_abs, norm_fderiv_eq_norm_partials_local (d := d)]
        _ ≤ ‖vn - hw.weakGrad x‖ := abs_norm_sub_norm_le vn (hw.weakGrad x)
        _ ≤ ∑ i : Fin d, ‖(vn - hw.weakGrad x) i‖ :=
            euclidean_norm_le_sum_norms (d := d) _
        _ = ∑ i : Fin d,
              ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
                hw.weakGrad x i‖ := by
            simp [vn]
    -- eLpNorm monotonicity: lift pointwise bound
    have h_mono : _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖) pp μ ≤
        _root_.MeasureTheory.eLpNorm (fun x => ∑ i : Fin d,
          ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖) pp μ :=
      _root_.MeasureTheory.eLpNorm_mono fun x => (h_ptwise x).trans_eq
        (Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).symm
    -- Minkowski: eLpNorm of sum ≤ sum of eLpNorms
    have h_mink : _root_.MeasureTheory.eLpNorm (fun x => ∑ i : Fin d,
        ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖) pp μ ≤
        ∑ i : Fin d, _root_.MeasureTheory.eLpNorm (fun x =>
          ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖) pp μ := by
      have h_eq : (fun x => ∑ i : Fin d,
          ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖) =
          ∑ i : Fin d, (fun x =>
            ‖(fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i‖) := by
        ext x; simp [Finset.sum_apply]
      rw [h_eq]
      exact _root_.MeasureTheory.eLpNorm_sum_le (fun i _ => (h_comp_aesm n i).norm) hpp
    calc _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖) pp μ
        ≤ _ := h_mono
      _ ≤ _ := h_mink
      _ = ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
              hw.weakGrad x i) pp μ := by
          congr 1; ext i; exact _root_.MeasureTheory.eLpNorm_norm _
  -- Sum of component errors → 0
  have h_grad_err_tendsto : _root_.Filter.Tendsto
      (fun n => ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
        (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
        pp μ)
      atTop (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _ : Fin d, (0 : ℝ≥0∞) from by simp]
    exact tendsto_finsetSum _ fun i _ => hψ_grad i
  -- === eLpNorm(‖fderiv ψ_n‖) ≤ eLpNorm(‖G‖) + grad_err ===
  have hG_norm_aesm : _root_.MeasureTheory.AEStronglyMeasurable (fun x => ‖hw.weakGrad x‖) μ := by
    -- Follow the pattern from aestronglyMeasurable_euclidean_of_components_local
    have h_ofLp : AEMeasurable (fun x => (WithLp.ofLp (hw.weakGrad x) : Fin d → ℝ)) μ :=
      aemeasurable_pi_iff.mpr fun i => by simpa using (hG_comp_aesm i).aemeasurable
    have h_toLp_meas : Measurable (fun x : Fin d → ℝ => WithLp.toLp 2 x) := by
      simpa using (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable
    have h_id : (fun x => WithLp.toLp 2 (WithLp.ofLp (hw.weakGrad x))) = hw.weakGrad := by
      funext x; simp
    exact ((h_toLp_meas.comp_aemeasurable h_ofLp).aestronglyMeasurable.congr
      (EventuallyEq.of_eq h_id)).norm
  have h_fderiv_le : ∀ n,
      _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖) pp μ ≤
      _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ +
        ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          pp μ := by
    intro n
    have hfn_aesm : _root_.MeasureTheory.AEStronglyMeasurable
        (fun x => ‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖) μ := by
      exact ((((hψ_smooth n).continuous_fderiv
        (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).norm).aestronglyMeasurable.restrict.sub
        hG_norm_aesm)
    calc _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖) pp μ
        = _root_.MeasureTheory.eLpNorm ((fun x => ‖hw.weakGrad x‖) +
            (fun x => ‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖)) pp μ := by
          congr 1; ext x; simp [add_sub_cancel]
      _ ≤ _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ +
            eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖ - ‖hw.weakGrad x‖) pp μ :=
          _root_.MeasureTheory.eLpNorm_add_le hG_norm_aesm hfn_aesm hpp
      _ ≤ _ := by gcongr; exact h_grad_err n
  -- === Integrability ===
  have hu_int : _root_.MeasureTheory.Integrable u μ :=
    hw.memLp.integrable (by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hp))
  have hψ_int : ∀ n, _root_.MeasureTheory.Integrable (ψ n) μ :=
    fun n => ((hψ_smooth n).continuous.continuousOn.integrableOn_compact
      (_root_.ProperSpace.isCompact_closedBall (0 : E) 1)).mono_set _root_.Metric.ball_subset_closedBall
  -- === Mean convergence ===
  have h_mean_le : ∀ n,
      _root_.MeasureTheory.eLpNorm (fun _ : E => ⨍ x in B, (ψ n x - u x) ∂volume) pp μ ≤
        eLpNorm (fun x => ψ n x - u x) pp μ := by
    intro n
    exact eLpNorm_const_average_le hpp hpp_top ((hψ_int n).sub hu_int)
  have h_mean_tendsto : _root_.Filter.Tendsto
      (fun n => _root_.MeasureTheory.eLpNorm
        (fun _ : E => ⨍ x in B, (ψ n x - u x) ∂volume) pp μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hψ_fn
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall h_mean_le)
  -- === Triangle inequality for each n ===
  -- u - ⨍u = -(ψ_n-u) + (ψ_n-⨍ψ_n) + ⨍(ψ_n-u)
  -- eLpNorm(u-⨍u) ≤ eLpNorm(ψ_n-u) + C*eLpNorm(‖fderiv ψ_n‖) + eLpNorm(⨍(ψ_n-u))
  --                ≤ eLpNorm(ψ_n-u) + C*(eLpNorm(‖G‖) + grad_err) + eLpNorm(⨍(ψ_n-u))
  have h_bound : ∀ n,
      _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in B, u y ∂volume) pp μ ≤
        C * _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ +
        (_root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
         _root_.MeasureTheory.eLpNorm (fun _ : E =>
           ⨍ x in B, (ψ n x - u x) ∂volume) pp μ +
         C * ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
           (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
             hw.weakGrad x i) pp μ) := by
    intro n
    -- Decompose: u - ⨍u =ᵃᵉ -(ψ_n-u) + (ψ_n-⨍ψ_n) + ⨍(ψ_n-u)
    have heq : (fun x => u x - ⨍ y in B, u y ∂volume) =ᵐ[μ]
        (fun x => -(ψ n x - u x) + (ψ n x - ⨍ y in B, ψ n y ∂volume) +
          (⨍ y in B, (ψ n y - u y) ∂volume)) := by
      have h_avg_sub : ⨍ y in B, (ψ n y - u y) ∂volume =
          ⨍ y in B, ψ n y ∂volume - ⨍ y in B, u y ∂volume := by
        change ⨍ y, (ψ n y - u y) ∂μ = ⨍ y, ψ n y ∂μ - ⨍ y, u y ∂μ
        simp only [_root_.MeasureTheory.average_eq, _root_.MeasureTheory.integral_sub (hψ_int n) hu_int, smul_sub]
      filter_upwards with x
      linarith [h_avg_sub]
    calc _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in B, u y ∂volume) pp μ
        = _root_.MeasureTheory.eLpNorm (fun x => -(ψ n x - u x) +
            (ψ n x - ⨍ y in B, ψ n y ∂volume) +
            ⨍ y in B, (ψ n y - u y) ∂volume) pp μ :=
          _root_.MeasureTheory.eLpNorm_congr_ae heq
      _ ≤ _root_.MeasureTheory.eLpNorm (fun x => -(ψ n x - u x) +
              (ψ n x - ⨍ y in B, ψ n y ∂volume)) pp μ +
            _root_.MeasureTheory.eLpNorm (fun _ : E =>
              (⨍ y in B, (ψ n y - u y) ∂volume : ℝ)) pp μ :=
          _root_.MeasureTheory.eLpNorm_add_le
            (((hψn_aesm n).sub hu_aesm).neg.add
              ((hψn_aesm n).sub _root_.MeasureTheory.aestronglyMeasurable_const))
            _root_.MeasureTheory.aestronglyMeasurable_const hpp
      _ ≤ (_root_.MeasureTheory.eLpNorm (fun x => -(ψ n x - u x)) pp μ +
              _root_.MeasureTheory.eLpNorm (fun x => ψ n x - ⨍ y in B, ψ n y ∂volume) pp μ) +
            _root_.MeasureTheory.eLpNorm (fun _ : E =>
              (⨍ y in B, (ψ n y - u y) ∂volume : ℝ)) pp μ := by
          gcongr
          exact _root_.MeasureTheory.eLpNorm_add_le ((hψn_aesm n).sub hu_aesm).neg
            ((hψn_aesm n).sub _root_.MeasureTheory.aestronglyMeasurable_const) hpp
      _ = _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
            _root_.MeasureTheory.eLpNorm (fun x => ψ n x - ⨍ y in B, ψ n y ∂volume) pp μ +
            _root_.MeasureTheory.eLpNorm (fun _ : E =>
              (⨍ x in B, (ψ n x - u x) ∂volume : ℝ)) pp μ := by
          congr 1; congr 1
          exact _root_.MeasureTheory.eLpNorm_congr_norm_ae (_root_.MeasureTheory.ae_of_all _ fun x => norm_neg _)
      _ ≤ _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
            C * _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ (ψ n) x‖) pp μ +
            _root_.MeasureTheory.eLpNorm (fun _ : E =>
              (⨍ x in B, (ψ n x - u x) ∂volume : ℝ)) pp μ := by
          gcongr; exact h_poinc n
      _ ≤ _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
            C * (_root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ +
              ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
                (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
                  hw.weakGrad x i) pp μ) +
            _root_.MeasureTheory.eLpNorm (fun _ : E =>
              (⨍ x in B, (ψ n x - u x) ∂volume : ℝ)) pp μ := by
          gcongr; exact h_fderiv_le n
      _ = _ := by
        rw [mul_add]
        abel
  -- === Error → 0 ===
  have h_err_tendsto : _root_.Filter.Tendsto (fun n =>
      _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
      _root_.MeasureTheory.eLpNorm (fun _ : E => ⨍ x in B, (ψ n x - u x) ∂volume) pp μ +
      C * ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
        (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) -
          hw.weakGrad x i) pp μ)
      atTop (nhds 0) := by
    have h1 : _root_.Filter.Tendsto (fun n =>
        _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
        _root_.MeasureTheory.eLpNorm (fun _ : E => ⨍ x in B, (ψ n x - u x) ∂volume) pp μ)
        atTop (nhds (0 + 0)) := hψ_fn.add h_mean_tendsto
    rw [add_zero] at h1
    have h2 : _root_.Filter.Tendsto (fun n =>
        C * ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) pp μ)
        atTop (nhds (C * 0)) :=
      ENNReal.Tendsto.const_mul h_grad_err_tendsto (Or.inr (by simp [C]))
    rw [_root_.MulZeroClass.mul_zero] at h2
    have h3 := h1.add h2
    rwa [add_zero] at h3
  -- === Conclude via ge_of_tendsto ===
  have h_rhs : _root_.Filter.Tendsto (fun n =>
      C * _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ +
      (_root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) pp μ +
       _root_.MeasureTheory.eLpNorm (fun _ : E => ⨍ x in B, (ψ n x - u x) ∂volume) pp μ +
       C * ∑ i : Fin d, _root_.MeasureTheory.eLpNorm
         (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) pp μ))
      atTop (nhds (C * _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) pp μ + 0)) :=
    tendsto_const_nhds.add h_err_tendsto
  rw [add_zero] at h_rhs
  exact ge_of_tendsto h_rhs (Eventually.of_forall h_bound)

run_cmd do
  let target := ``Submission.DeGiorgi.poincare_unitBall_W1p
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.poincare_unitBall_W1p target :: scope.openDecls } }

/-- Unit-ball Poincare estimate packaged for direct reuse. -/
theorem poincare_unitBall_W1p_public
    {p : ℝ} (hp : 1 < p)
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
      (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) ≤
    ENNReal.ofReal (CPoincVal d) *
      _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) :=
  poincare_unitBall_W1p (d := d) hp hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.poincare_unitBall_W1p_public then
    throwError "Refusing to shadow existing declaration DeGiorgi.poincare_unitBall_W1p_public"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.poincare_unitBall_W1p_public ``Submission.DeGiorgi.poincare_unitBall_W1p_public

/-! ## Extension gradient `eLpNorm` bound -/

omit [NeZero d] in
/-- Convert the lintegral-level extension gradient bound into an `eLpNorm`
bound using Poincare. -/
private theorem extension_gradient_eLpNorm_bound
    {p : ℝ} (hp : 1 < p)
    {v : E → ℝ}
    (hwv : MemW1pWitness (ENNReal.ofReal p) v (Metric.ball (0 : E) 1))
    {hwExt : MemW1pWitness (ENNReal.ofReal p) (unitBallExtension (d := d) v) Set.univ}
    (hgrad_bound :
      (∫⁻ x, (ENNReal.ofReal ‖hwExt.weakGrad x‖) ^ p ∂volume)
        ≤ (∫⁻ x in Metric.ball (0 : E) 1,
              (ENNReal.ofReal ‖hwv.weakGrad x‖) ^ p ∂volume) +
          CUnitBallExtensionGrad d p *
            (∫⁻ x in Metric.ball (0 : E) 1,
                (ENNReal.ofReal |v x|) ^ p ∂volume +
             ∫⁻ x in Metric.ball (0 : E) 1,
                (ENNReal.ofReal ‖hwv.weakGrad x‖) ^ p ∂volume))
    (hv_poincare :
      _root_.MeasureTheory.eLpNorm v (ENNReal.ofReal p) (volume.restrict (Metric.ball (0 : E) 1)) ≤
        ENNReal.ofReal (CPoincVal d) *
          _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
            (volume.restrict (Metric.ball (0 : E) 1))) :
    _root_.MeasureTheory.eLpNorm (fun x => ‖hwExt.weakGrad x‖) (ENNReal.ofReal p) _root_.MeasureTheory.MeasureSpace.volume ≤
    C_extensionGrad d p *
      _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  let B := Metric.ball (0 : E) 1
  let μ := volume.restrict B
  let pp := ENNReal.ofReal p
  let Cp := ENNReal.ofReal (CPoincVal d)
  let Ce := CUnitBallExtensionGrad d p
  let Gext := _root_.MeasureTheory.eLpNorm (fun x => ‖hwExt.weakGrad x‖) pp _root_.MeasureTheory.MeasureSpace.volume
  let Gv := _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) pp μ
  let Fv := _root_.MeasureTheory.eLpNorm v pp μ
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := le_of_lt hp
  have h_abs_eq : ∀ x, ENNReal.ofReal |v x| = ENNReal.ofReal ‖v x‖ :=
    fun x => by rw [Real.norm_eq_abs]
  have hpow : Gext ^ p ≤ Gv ^ p + Ce * (Fv ^ p + Gv ^ p) := by
    have hGext_eq : Gext ^ p = ∫⁻ x, (ENNReal.ofReal ‖hwExt.weakGrad x‖) ^ p ∂volume := by
      change _root_.MeasureTheory.eLpNorm (fun x => ‖hwExt.weakGrad x‖) pp _root_.MeasureTheory.MeasureSpace.volume ^ p = _
      rw [_root_.MeasureTheory.eLpNorm_norm, ← lintegral_rpow_norm_eq_eLpNorm_pow hp0]
    have hGv_eq : Gv ^ p = ∫⁻ x in B, (ENNReal.ofReal ‖hwv.weakGrad x‖) ^ p ∂volume := by
      change _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) pp μ ^ p = _
      rw [_root_.MeasureTheory.eLpNorm_norm, ← lintegral_rpow_norm_eq_eLpNorm_pow hp0]
    have hFv_eq : Fv ^ p = ∫⁻ x in B, (ENNReal.ofReal |v x|) ^ p ∂volume := by
      change _root_.MeasureTheory.eLpNorm v pp μ ^ p = _
      have : (fun x => (ENNReal.ofReal ‖v x‖) ^ p) = (fun x => (ENNReal.ofReal |v x|) ^ p) :=
        funext fun x => by rw [Real.norm_eq_abs]
      rw [← lintegral_rpow_norm_eq_eLpNorm_pow hp0, this]
    rw [hGext_eq, hGv_eq, hFv_eq]
    exact hgrad_bound
  have hFvp : Fv ^ p ≤ Cp ^ p * Gv ^ p :=
    calc Fv ^ p ≤ (Cp * Gv) ^ p :=
          ENNReal.rpow_le_rpow (show Fv ≤ Cp * Gv from hv_poincare) hp0.le
      _ = Cp ^ p * Gv ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp0.le
  have hpow2 : Gext ^ p ≤ (1 + Ce * (Cp ^ p + 1)) * Gv ^ p := by
    calc Gext ^ p ≤ Gv ^ p + Ce * (Fv ^ p + Gv ^ p) := hpow
      _ ≤ Gv ^ p + Ce * (Cp ^ p * Gv ^ p + Gv ^ p) := by gcongr
      _ = (1 + Ce * (Cp ^ p + 1)) * Gv ^ p := by ring
  have hCe1 : 1 ≤ Ce := by
    change 1 ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) * (2 : ℝ≥0∞) ^ (p - 1)
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ (2 * d)) :=
            (ENNReal.one_le_ofReal).mpr (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
            (ENNReal.one_le_rpow (by norm_num : (1:ℝ≥0∞) ≤ 2) (by linarith : 0 < p - 1))
  have hK : 1 + Ce * (Cp ^ p + 1) ≤ (C_extensionGrad d p) ^ p := by
    change 1 + Ce * (Cp ^ p + 1) ≤ (1 + Ce * (Cp + 1)) ^ p
    have hCep : Ce ≤ Ce ^ p := by
      conv_lhs => rw [show Ce = Ce ^ (1 : ℝ) from (ENNReal.rpow_one Ce).symm]
      exact ENNReal.rpow_le_rpow_of_exponent_le hCe1 hp1
    have h_cp1 : Cp ^ p + 1 ≤ (Cp + 1) ^ p := by
      simpa [ENNReal.one_rpow] using ENNReal.add_rpow_le_rpow_add Cp 1 hp1
    have h_add : 1 + (Ce * (Cp + 1)) ^ p ≤ (1 + Ce * (Cp + 1)) ^ p := by
      simpa [ENNReal.one_rpow] using
        ENNReal.add_rpow_le_rpow_add 1 (Ce * (Cp + 1)) hp1
    calc 1 + Ce * (Cp ^ p + 1)
        ≤ 1 + Ce ^ p * (Cp + 1) ^ p := by gcongr
      _ = 1 + (Ce * (Cp + 1)) ^ p := by
          congr 1; exact (ENNReal.mul_rpow_of_nonneg _ _ hp0.le).symm
      _ ≤ (1 + Ce * (Cp + 1)) ^ p := h_add
  calc Gext ≤ C_extensionGrad d p * Gv :=
        (ENNReal.rpow_le_rpow_iff hp0).mp (calc
          Gext ^ p ≤ (1 + Ce * (Cp ^ p + 1)) * Gv ^ p := hpow2
          _ ≤ (C_extensionGrad d p) ^ p * Gv ^ p := by gcongr
          _ = (C_extensionGrad d p * Gv) ^ p :=
              (ENNReal.mul_rpow_of_nonneg _ _ hp0.le).symm)

run_cmd do
  let target := ``Submission.DeGiorgi.extension_gradient_eLpNorm_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.extension_gradient_eLpNorm_bound target :: scope.openDecls } }

/-! ## Main theorem -/

/-- Sobolev-Poincare inequality on the unit ball. -/
theorem sobolev_poincare_unitBall
    {p : ℝ} (hp : 1 < p) (hpd : p < (d : ℝ))
    {u : E → ℝ}
    (hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
      (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
      (volume.restrict (Metric.ball (0 : E) 1)) ≤
    CSobolevPoincare d p *
      _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  let B := Metric.ball (0 : E) 1
  let ubar := ⨍ y in B, u y ∂volume
  let v : E → ℝ := fun x => u x - ubar
  let pstar := ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))
  let hwv := memW1pWitnessSubConstUnitBall (d := d) hp hw ubar
  have hwv_grad : hwv.weakGrad = hw.weakGrad :=
    memW1pWitness_sub_const_unitBall_weakGrad hp hw ubar
  obtain ⟨hwExt, hcpt, hagree, _hfun_bound, hgrad_bound⟩ :=
    exists_unitBall_W1p_extension (d := d) hp hwv
  have hW01 : MemW01p (ENNReal.ofReal p) (unitBallExtension (d := d) v) Set.univ :=
    memW01p_of_memW1p_of_tsupport_subset isOpen_univ hp hwExt.memW1p hcpt
      (Set.subset_univ _)
  obtain ⟨hwSob, hSob⟩ := sobolev_of_memW01p_univ (d := d) (le_of_lt hp) hpd hW01
  have hae_grad : hwSob.weakGrad =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] hwExt.weakGrad := by
    have h := MemW1pWitness.ae_eq_p (d := d) isOpen_univ (show 1 ≤ p from le_of_lt hp)
      hwSob hwExt
    simpa [Measure.restrict_univ] using h
  have hSob' :
      eLpNorm (unitBallExtension (d := d) v) pstar _root_.MeasureTheory.MeasureSpace.volume ≤
        ENNReal.ofReal (CGns d p) *
          eLpNorm (fun x => ‖hwExt.weakGrad x‖) (ENNReal.ofReal p) volume := by
    calc
      eLpNorm (unitBallExtension (d := d) v) pstar _root_.MeasureTheory.MeasureSpace.volume
          ≤ ENNReal.ofReal (CGns d p) *
              eLpNorm (fun x => ‖hwSob.weakGrad x‖) (ENNReal.ofReal p) volume := hSob
      _ = ENNReal.ofReal (CGns d p) *
            eLpNorm (fun x => ‖hwExt.weakGrad x‖) (ENNReal.ofReal p) volume := by
          congr 1
          exact _root_.MeasureTheory.eLpNorm_congr_ae (hae_grad.fun_comp (‖·‖))
  have hrestrict :
      _root_.MeasureTheory.eLpNorm v pstar (volume.restrict B) ≤
        eLpNorm (unitBallExtension (d := d) v) pstar volume := by
    calc
      _root_.MeasureTheory.eLpNorm v pstar (volume.restrict B)
          = _root_.MeasureTheory.eLpNorm (unitBallExtension (d := d) v) pstar (volume.restrict B) := by
            apply _root_.MeasureTheory.eLpNorm_congr_ae
            have : ∀ᵐ x ∂(volume.restrict B), v x = unitBallExtension (d := d) v x := by
              filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
              exact (hagree x hx).symm
            exact this
      _ ≤ _root_.MeasureTheory.eLpNorm (unitBallExtension (d := d) v) pstar volume :=
          _root_.MeasureTheory.eLpNorm_mono_measure _ Measure.restrict_le_self
  have hv_poinc_raw :
      _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in B, u y ∂volume) (ENNReal.ofReal p)
        (volume.restrict B) ≤
      ENNReal.ofReal (CPoincVal d) *
        _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p)
          (volume.restrict B) :=
    poincare_unitBall_W1p (d := d) hp hw
  have hv_poinc :
      _root_.MeasureTheory.eLpNorm v (ENNReal.ofReal p) (volume.restrict B) ≤
        ENNReal.ofReal (CPoincVal d) *
          _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
            (volume.restrict B) := by
    rw [hwv_grad]
    exact hv_poinc_raw
  have hgrad_absorb :
      _root_.MeasureTheory.eLpNorm (fun x => ‖hwExt.weakGrad x‖) (ENNReal.ofReal p) _root_.MeasureTheory.MeasureSpace.volume ≤
        C_extensionGrad d p *
          _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
            (volume.restrict B) :=
    extension_gradient_eLpNorm_bound (d := d) hp hwv hgrad_bound hv_poinc
  have hwv_grad_eq : (fun x => ‖hwv.weakGrad x‖) = (fun x => ‖hw.weakGrad x‖) := by
    ext x
    rw [hwv_grad]
  calc
    _root_.MeasureTheory.eLpNorm v pstar (volume.restrict B)
        ≤ _root_.MeasureTheory.eLpNorm (unitBallExtension (d := d) v) pstar volume := hrestrict
    _ ≤ ENNReal.ofReal (CGns d p) *
          eLpNorm (fun x => ‖hwExt.weakGrad x‖) (ENNReal.ofReal p) volume := hSob'
    _ ≤ ENNReal.ofReal (CGns d p) *
          (C_extensionGrad d p *
            _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
              (volume.restrict B)) := by
          gcongr
    _ = ENNReal.ofReal (CGns d p) * C_extensionGrad d p *
          _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
            (volume.restrict B) := by
          rw [mul_assoc]
    _ = CSobolevPoincare d p *
          _root_.MeasureTheory.eLpNorm (fun x => ‖hwv.weakGrad x‖) (ENNReal.ofReal p)
            (volume.restrict B) := by
          rfl
    _ = CSobolevPoincare d p *
          _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p)
            (volume.restrict B) := by
          rw [hwv_grad_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.sobolev_poincare_unitBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.sobolev_poincare_unitBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.sobolev_poincare_unitBall ``Submission.DeGiorgi.sobolev_poincare_unitBall

/-! ## Existential version -/

/-- Sobolev-Poincare inequality for `MemW1p` in existential form. -/
theorem sobolev_poincare_unitBall'
    {p : ℝ} (hp : 1 < p) (hpd : p < (d : ℝ))
    {u : E → ℝ}
    (hu : MemW1p (ENNReal.ofReal p) u (Metric.ball (0 : E) 1)) :
    ∃ C : ℝ≥0∞, ∃ G : E → E,
      HasWeakGrad G u (Metric.ball (0 : E) 1) ∧
      _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
        (volume.restrict (Metric.ball (0 : E) 1)) ≤
      C * _root_.MeasureTheory.eLpNorm (fun x => ‖G x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  have hfLp := hu.1
  choose gi hgi using hu.2
  let G : E → E := fun x => WithLp.toLp 2 (fun i => gi i x)
  let hw : MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1) :=
    { memLp := hfLp
      weakGrad := G
      weakGrad_component_memLp := by
        intro i
        simpa [G, PiLp.toLp_apply] using (hgi i).1
      isWeakGrad := by
        intro i
        simpa [G, PiLp.toLp_apply] using (hgi i).2 }
  exact ⟨CSobolevPoincare d p, G, hw.isWeakGrad,
    sobolev_poincare_unitBall hp hpd hw⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.sobolev_poincare_unitBall' then
    throwError "Refusing to shadow existing declaration DeGiorgi.sobolev_poincare_unitBall'"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.sobolev_poincare_unitBall' ``Submission.DeGiorgi.sobolev_poincare_unitBall'

/-! ## Smooth version -/

/-- Build a `W^{1,p}` witness for a smooth function on the unit ball. -/
private noncomputable def smooth_memW1pWitness_unitBall
    {p : ℝ} (hp : 1 < p) (hpd : p < (d : ℝ))
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    MemW1pWitness (ENNReal.ofReal p) u (Metric.ball (0 : E) 1) := by
  let _ := hp
  let _ := hpd
  set B := Metric.ball (0 : E) 1
  set G : E → E := fun x => WithLp.toLp 2
    (fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1))
  refine
    { memLp := ?_
      weakGrad := G
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · -- Continuous on compact closedBall → bounded → MemLp ⊤ → MemLp p
    have hfin : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict B) := by
      constructor; rw [Measure.restrict_apply_univ]; exact _root_.MeasureTheory.measure_ball_lt_top
    have hcont := hu.continuous
    obtain ⟨C, hC⟩ := ((_root_.ProperSpace.isCompact_closedBall (0 : E) 1).image_of_continuousOn
      hcont.continuousOn).isBounded.exists_norm_le
    have hbound : ∀ᵐ x ∂(volume.restrict B), ‖u x‖ ≤ C := by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
      exact hC _ ⟨x, _root_.Metric.ball_subset_closedBall hx, rfl⟩
    exact (_root_.MeasureTheory.memLp_top_of_bound (hcont.aestronglyMeasurable.restrict (s := B)) C hbound).mono_exponent
      le_top
  · intro i
    have hfin : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict B) := by
      constructor; rw [Measure.restrict_apply_univ]; exact _root_.MeasureTheory.measure_ball_lt_top
    have hcont_i : Continuous (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
      (hu.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    obtain ⟨C, hC⟩ := ((_root_.ProperSpace.isCompact_closedBall (0 : E) 1).image_of_continuousOn
      hcont_i.continuousOn).isBounded.exists_norm_le
    have hbound : ∀ᵐ x ∂(volume.restrict B), ‖(fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1))
      x‖ ≤ C := by
      filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
      exact hC _ ⟨x, _root_.Metric.ball_subset_closedBall hx, rfl⟩
    exact (_root_.MeasureTheory.memLp_top_of_bound (hcont_i.aestronglyMeasurable.restrict (s := B)) C
      hbound).mono_exponent
      le_top
  · intro i
    simpa [G, PiLp.toLp_apply] using
      HasWeakPartialDeriv.of_contDiff (d := d) (Ω := B) (i := i)
        _root_.Metric.isOpen_ball (hu.of_le (by norm_cast))

run_cmd do
  let target := ``Submission.DeGiorgi.smooth_memW1pWitness_unitBall
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.smooth_memW1pWitness_unitBall target :: scope.openDecls } }

/-- Sobolev-Poincare for smooth functions on the unit ball. -/
theorem sobolev_poincare_smooth_unitBall
    {p : ℝ} (hp : 1 < p) (hpd : p < (d : ℝ))
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    _root_.MeasureTheory.eLpNorm (fun x => u x - ⨍ y in Metric.ball (0 : E) 1, u y ∂volume)
      (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
      (volume.restrict (Metric.ball (0 : E) 1)) ≤
    CSobolevPoincare d p *
      _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) := by
  let hw := smooth_memW1pWitness_unitBall (d := d) hp hpd hu
  have hmain := sobolev_poincare_unitBall (d := d) hp hpd hw
  suffices hgrad_eq :
      _root_.MeasureTheory.eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) =
      _root_.MeasureTheory.eLpNorm (fun x => ‖fderiv ℝ u x‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball (0 : E) 1)) by
    rw [← hgrad_eq]
    exact hmain
  apply _root_.MeasureTheory.eLpNorm_congr_ae
  filter_upwards with x
  change ‖WithLp.toLp 2 (fun i => (fderiv ℝ u x) (EuclideanSpace.single i 1))‖ =
    ‖fderiv ℝ u x‖
  exact norm_fderiv_eq_norm_partials_local (d := d).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.sobolev_poincare_smooth_unitBall then
    throwError "Refusing to shadow existing declaration DeGiorgi.sobolev_poincare_smooth_unitBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.sobolev_poincare_smooth_unitBall ``Submission.DeGiorgi.sobolev_poincare_smooth_unitBall

end DeGiorgi
