-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace
import Submission.DifferentialGeometry.External.DeGiorgi.StampacchiaTruncation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Chapter 02: Positive-Part And Approximation Layer

This module develops the positive-part and approximation tools used by the
Sobolev and De Giorgi arguments:

- weak-derivative uniqueness and approximation transfer;
- the canonical indicator-difference convergence theorem;
- the smooth positive-part chain rule;
- the auxiliary positive-part witness constructor.

The emphasis here is on the approximation statements needed to pass from Sobolev
witness data to positive-part closures that can be reused later in the De
Giorgi iteration.
-/

noncomputable section

open _root_.MeasureTheory _root_.Filter _root_.Topology
open scoped _root_.ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-! ## Weak-Derivative Uniqueness And Approximation Transfer -/

omit [NeZero d] in
private theorem HasWeakPartialDeriv.toStampacchia
    {Ω : Set E} {i : Fin d} {g f : E → ℝ}
    (h : HasWeakPartialDeriv i g f Ω) :
    HasWeakPartialDeriv' (d := d) i g f Ω := by
  simpa [HasWeakPartialDeriv, HasWeakPartialDeriv'] using h

run_cmd do
  let target := ``Submission.DeGiorgi.HasWeakPartialDeriv.toStampacchia
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.HasWeakPartialDeriv.toStampacchia target :: scope.openDecls } }

omit [NeZero d] in
private theorem stampacchia_congr_ae
    {Ω : Set E} {i : Fin d} {g f f' : E → ℝ}
    (h : HasWeakPartialDeriv' (d := d) i g f Ω)
    (hff' : f =ᵐ[volume.restrict Ω] f') :
    HasWeakPartialDeriv' (d := d) i g f' Ω := by
  intro φ hφ hφ_cpt hφ_sub
  have hcongr :
      (fun x => f' x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        =ᵐ[volume.restrict Ω]
      (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    filter_upwards [hff'] with x hx
    simp [hx]
  calc
    ∫ x in Ω, f' x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        ∫ x in Ω, f x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
          exact _root_.MeasureTheory.integral_congr_ae hcongr
    _ = -∫ x in Ω, g x * φ x := h φ hφ hφ_cpt hφ_sub

run_cmd do
  let target := ``Submission.DeGiorgi.stampacchia_congr_ae
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.stampacchia_congr_ae target :: scope.openDecls } }

/-- Stampacchia's zero-set theorem for Sobolev witnesses: each weak-gradient
component vanishes a.e. on the zero set of the function. -/
theorem MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω) :
    ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), u x = 0 → hw.weakGrad x i = 0 := by
  intro i
  let uMk : E → ℝ := AEMeasurable.mk u hw.memLp.aemeasurable
  have hu_meas : Measurable uMk := hw.memLp.aemeasurable.measurable_mk
  have hu_ae : u =ᵐ[volume.restrict Ω] uMk := hw.memLp.aemeasurable.ae_eq_mk
  have hGMk :
      ∀ j : Fin d, HasWeakPartialDeriv' (d := d) j (fun x => hw.weakGrad x j) uMk Ω := by
    intro j
    exact stampacchia_congr_ae
      (HasWeakPartialDeriv.toStampacchia (hw.isWeakGrad j)) hu_ae
  have huMk_memW1p : MemW1p 2 uMk Ω := by
    refine ⟨hw.memLp.ae_eq hu_ae, ?_⟩
    intro j
    exact ⟨fun x => hw.weakGrad x j, hw.weakGrad_component_memLp j, by
      simpa [HasWeakPartialDeriv'] using hGMk j⟩
  have hzero_mk :
      ∀ᵐ x ∂(volume.restrict Ω), uMk x = 0 → hw.weakGrad x i = 0 :=
    DeGiorgi.weakGrad_ae_eq_zero_on_zeroSet hΩ huMk_memW1p hGMk i
      (hw.weakGrad_component_memLp i) hu_meas
  filter_upwards [hu_ae, hzero_mk] with x hx hzero hx_zero
  exact hzero (by simpa [hx] using hx_zero)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet ``Submission.DeGiorgi.MemW1pWitness.weakGrad_ae_eq_zero_on_zeroSet

/-- Subtracting a constant preserves a `W^{1,2}` witness on finite-measure
domains. -/
noncomputable def MemW1pWitness.subConst
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω)
    {u : E → ℝ} (hw : MemW1pWitness 2 u Ω) (c : ℝ) :
    MemW1pWitness 2 (fun x => u x - c) Ω where
  memLp := hw.memLp.sub (_root_.MeasureTheory.memLp_const c)
  weakGrad := hw.weakGrad
  weakGrad_component_memLp := hw.weakGrad_component_memLp
  isWeakGrad := by
    intro i φ hφ hφ_supp hφ_sub
    let ei : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i (1 : ℝ)
    have hkey := hw.isWeakGrad i φ hφ hφ_supp hφ_sub
    have hconst :
        HasWeakPartialDeriv i (fun _ : E => (0 : ℝ)) (fun _ : E => c) Ω := by
      simpa [ei] using
        (HasWeakPartialDeriv.of_contDiff (Ω := Ω) (i := i)
          (f := fun _ : E => c) hΩ contDiff_const)
    have hconst_zero : ∫ x in Ω, c * (fderiv ℝ φ x) ei = 0 := by
      simpa using hconst φ hφ hφ_supp hφ_sub
    have hderiv_cont : Continuous (fun x => (fderiv ℝ φ x) ei) :=
      (hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
        continuous_const
    have hderiv_supp : HasCompactSupport (fun x => (fderiv ℝ φ x) ei) :=
      hφ_supp.fderiv_apply (𝕜 := ℝ) ei
    have hu_int : _root_.MeasureTheory.Integrable (fun x => u x * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      have hu_loc : _root_.MeasureTheory.LocallyIntegrable u (volume.restrict Ω) :=
        hw.memLp.locallyIntegrable (by norm_num)
      simpa [smul_eq_mul] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_supp
    have hc_int : _root_.MeasureTheory.Integrable (fun x => c * (fderiv ℝ φ x) ei) (volume.restrict Ω) := by
      exact (hderiv_cont.integrable_of_hasCompactSupport hderiv_supp).const_mul c
    have hsub_fun :
        (fun x => (u x - c) * (fderiv ℝ φ x) ei) =
          (fun x => u x * (fderiv ℝ φ x) ei - c * (fderiv ℝ φ x) ei) := by
      ext x
      ring
    rw [hsub_fun, _root_.MeasureTheory.integral_sub hu_int hc_int, hkey, hconst_zero]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.subConst then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.subConst"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.subConst ``Submission.DeGiorgi.MemW1pWitness.subConst

/-- Multiply a `W^{1,2}` witness by a bounded smooth scalar factor. -/
noncomputable def MemW1pWitness.mulSmoothBounded
    {Ω : Set E} (hΩ : IsOpen Ω)
    {u η : E → ℝ} (hw : MemW1pWitness 2 u Ω)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C₀ C₁ : ℝ}
    (_hC₀ : 0 ≤ C₀) (_hC₁ : 0 ≤ C₁)
    (hη_bound : ∀ x, |η x| ≤ C₀)
    (hη_grad_bound : ∀ x, ‖fderiv ℝ η x‖ ≤ C₁) :
    MemW1pWitness 2 (fun x => η x * u x) Ω where
  memLp := by
    let _ := _hC₀
    let _ := _hC₁
    refine MemLp.of_le_mul (g := u) (c := C₀) hw.memLp ?_ ?_
    · exact hη.continuous.aestronglyMeasurable.mul hw.memLp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        calc
          ‖η x * u x‖ = |η x| * ‖u x‖ := by
            rw [norm_mul, Real.norm_eq_abs]
          _ ≤ C₀ * ‖u x‖ := by
              gcongr
              exact hη_bound x
  weakGrad := fun x =>
    η x • hw.weakGrad x +
      (show E from WithLp.toLp 2 fun i => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
  weakGrad_component_memLp := by
    intro i
    have hfirst : _root_.MeasureTheory.MemLp (fun x => η x * hw.weakGrad x i) 2 (volume.restrict Ω) := by
      refine MemLp.of_le_mul (g := fun x => hw.weakGrad x i) (c := C₀)
        (hw.weakGrad_component_memLp i) ?_ ?_
      · exact hη.continuous.aestronglyMeasurable.mul
          (hw.weakGrad_component_memLp i).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          calc
            ‖η x * hw.weakGrad x i‖ = |η x| * ‖hw.weakGrad x i‖ := by
              rw [norm_mul, Real.norm_eq_abs]
            _ ≤ C₀ * ‖hw.weakGrad x i‖ := by
                gcongr
                exact hη_bound x
    have hderiv_cont : Continuous (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) :=
      (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply continuous_const
    have hsecond :
        _root_.MeasureTheory.MemLp (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) 2
          (volume.restrict Ω) := by
      refine MemLp.of_le_mul (g := u) (c := C₁) hw.memLp ?_ ?_
      · exact hderiv_cont.aestronglyMeasurable.mul hw.memLp.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun x => by
          calc
            ‖(fderiv ℝ η x) (EuclideanSpace.single i 1) * u x‖
                = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖u x‖ := by
                    rw [norm_mul]
            _ ≤ ‖fderiv ℝ η x‖ * ‖u x‖ := by
                  gcongr
                  simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ η x)
                    (EuclideanSpace.single i (1 : ℝ)))
            _ ≤ C₁ * ‖u x‖ := by
                  gcongr
                  exact hη_grad_bound x
    let h : _root_.MeasureTheory.MemLp
        (fun x => η x * hw.weakGrad x i +
          (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
        2 (volume.restrict Ω) := hfirst.add hsecond
    exact h
  isWeakGrad := by
    intro i
    simpa using HasWeakPartialDeriv.mul_smooth hΩ
      (hf := hw.isWeakGrad i) hη
      (hw.memLp.locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.mulSmoothBounded then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.mulSmoothBounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.mulSmoothBounded ``Submission.DeGiorgi.MemW1pWitness.mulSmoothBounded

/-
A compactly supported `W₀^{1,2}` witness already contains the approximation
data needed by the positive-part closure arguments.
-/
omit [NeZero d] in
theorem smoothApproxData_of_memW01p
    {Ω : Set E} {u : E → ℝ}
    (hu : MemW01p 2 u Ω) :
    ∃ (hw : MemW1pWitness 2 u Ω) (φ : ℕ → E → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ Ω) ∧
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => φ n x - u x) 2 (volume.restrict Ω))
        _root_.Filter.atTop (nhds 0) ∧
      ∀ i : Fin d,
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm
          (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω))
          atTop (nhds 0) := by
  simpa [MemW01p] using hu.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.smoothApproxData_of_memW01p then
    throwError "Refusing to shadow existing declaration DeGiorgi.smoothApproxData_of_memW01p"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.smoothApproxData_of_memW01p ``Submission.DeGiorgi.smoothApproxData_of_memW01p

omit [NeZero d] in
private lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero
    {μ : _root_.MeasureTheory.Measure E} {f : E → ℝ} {g : ℕ → E → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 μ)
    (hg : ∀ n, _root_.MeasureTheory.MemLp (g n) 2 μ)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (g n) 2 μ) _root_.Filter.atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) _root_.Filter.atTop (nhds 0) := by
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) := by
    exact Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  let C : ℝ := MeasureTheory.lpNorm f 2 μ
  have hlim' : _root_.Filter.Tendsto (fun n => MeasureTheory.lpNorm (g n) 2 μ) _root_.Filter.atTop (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (_root_.MeasureTheory.eLpNorm (g n) 2 μ).toReal) _root_.Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (_root_.MeasureTheory.eLpNorm (g n) 2 μ).toReal) = (fun n => MeasureTheory.lpNorm (g n) 2 μ) := by
      funext n
      simpa using
        (MeasureTheory.toReal_eLpNorm
          (μ := μ) (p := (2 : ℝ≥0∞)) (f := g n) (hg n).aestronglyMeasurable)
    simpa [hEq] using hlim_toReal
  have hbound : ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * MeasureTheory.lpNorm (g n) 2 μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using _root_.MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have hf' : _root_.MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
    have hg' : _root_.MeasureTheory.MemLp (g n) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg n
    have h_holder :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := (2 : ℝ)) (q := (2 : ℝ)) hpq hf' hg'
    have h_f_lp :
        MeasureTheory.lpNorm f 2 μ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
      simpa using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := (2 : ℝ≥0∞)) (f := f) (by norm_num) (by simp)
          hf.aestronglyMeasurable)
    have h_g_lp :
        MeasureTheory.lpNorm (g n) 2 μ = (∫ x, ‖g n x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
      simpa using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := (2 : ℝ≥0∞)) (f := g n) (by norm_num) (by simp)
          (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) 2 μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper : _root_.Filter.Tendsto (fun n => C * MeasureTheory.lpNorm (g n) 2 μ) _root_.Filter.atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs : _root_.Filter.Tendsto (fun n => |∫ x, f x * g n x ∂μ|) _root_.Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

run_cmd do
  let target := ``Submission.DeGiorgi.tendsto_integral_mul_of_eLpNorm_tendsto_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.tendsto_integral_mul_of_eLpNorm_tendsto_zero target :: scope.openDecls } }

/-
Transfer weak derivatives from smooth compact-support approximants to the limit
function.
-/
omit [NeZero d] in
theorem HasWeakPartialDeriv.of_eLpNormApprox
    {Ω : Set E} (_hΩ : IsOpen Ω)
    {i : Fin d} {f g : E → ℝ} {ψ : ℕ → E → ℝ} {gψ : ℕ → E → ℝ}
    (hf_memLp : _root_.MeasureTheory.MemLp f 2 (volume.restrict Ω))
    (hg_memLp : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (hψ_wd : ∀ n, HasWeakPartialDeriv i (gψ n) (ψ n) Ω)
    (hψ_fun_memLp : ∀ n, _root_.MeasureTheory.MemLp (fun x => ψ n x - f x) 2 (volume.restrict Ω))
    (hψ_fun :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - f x) 2 (volume.restrict Ω))
        _root_.Filter.atTop (nhds 0))
    (hψ_grad_memLp : ∀ n, _root_.MeasureTheory.MemLp (fun x => gψ n x - g x) 2 (volume.restrict Ω))
    (hψ_grad :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => gψ n x - g x) 2 (volume.restrict Ω))
        _root_.Filter.atTop (nhds 0)) :
    HasWeakPartialDeriv i g f Ω := by
  let _ := _hΩ
  intro φ hφ hφ_supp hφ_sub
  let μ : _root_.MeasureTheory.Measure E := volume.restrict Ω
  let dφ : E → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  have hdφ_memLp : _root_.MeasureTheory.MemLp dφ 2 μ := by
    have hcont : Continuous dφ := by
      simpa [dφ] using
        ((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const)
    have hcpt : HasCompactSupport dφ := by
      simpa [dφ] using hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    exact (hcont.memLp_of_hasCompactSupport hcpt).restrict _
  have hφ_memLp : _root_.MeasureTheory.MemLp φ 2 μ :=
    (hφ.continuous.memLp_of_hasCompactSupport hφ_supp).restrict _
  have h_fun_int :
      Tendsto (fun n => ∫ x, dφ x * (ψ n x - f x) ∂μ) _root_.Filter.atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero hdφ_memLp hψ_fun_memLp hψ_fun
  have h_grad_int :
      Tendsto (fun n => ∫ x, φ x * (gψ n x - g x) ∂μ) _root_.Filter.atTop (nhds 0) :=
    tendsto_integral_mul_of_eLpNorm_tendsto_zero hφ_memLp hψ_grad_memLp hψ_grad
  have h_lhs_tendsto :
      _root_.Filter.Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (∫ x in Ω, f x * dφ x)) := by
    have h_eq :
        ∀ n,
          ∫ x, ψ n x * dφ x ∂μ =
            (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ := by
      intro n
      have hfi : _root_.MeasureTheory.Integrable (fun x => f x * dφ x) μ := hf_memLp.integrable_mul hdφ_memLp
      have hdi : _root_.MeasureTheory.Integrable (fun x => dφ x * (ψ n x - f x)) μ :=
        hdφ_memLp.integrable_mul (hψ_fun_memLp n)
      calc
        ∫ x, ψ n x * dφ x ∂μ
            = ∫ x, (f x * dφ x) + dφ x * (ψ n x - f x) ∂μ := by
                congr with x
                ring
        _ = (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ :=
              _root_.MeasureTheory.integral_add hfi hdi
    have h_aux :
        _root_.Filter.Tendsto
          (fun n => (∫ x, f x * dφ x ∂μ) + ∫ x, dφ x * (ψ n x - f x) ∂μ)
          atTop (nhds ((∫ x, f x * dφ x ∂μ) + 0)) :=
      Tendsto.const_add _ h_fun_int
    simpa [μ, h_eq, add_comm, add_left_comm, add_assoc] using h_aux
  have h_rhs_tendsto :
      _root_.Filter.Tendsto (fun n => -∫ x in Ω, gψ n x * φ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    have h_eq :
        ∀ n,
          -(∫ x, gψ n x * φ x ∂μ) =
            -(∫ x, g x * φ x ∂μ) - ∫ x, φ x * (gψ n x - g x) ∂μ := by
      intro n
      have hgi : _root_.MeasureTheory.Integrable (fun x => g x * φ x) μ := hg_memLp.integrable_mul hφ_memLp
      have hdi : _root_.MeasureTheory.Integrable (fun x => φ x * (gψ n x - g x)) μ :=
        hφ_memLp.integrable_mul (hψ_grad_memLp n)
      have : ∫ x, gψ n x * φ x ∂μ =
          (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (gψ n x - g x) ∂μ := by
        calc
          ∫ x, gψ n x * φ x ∂μ
              = ∫ x, (g x * φ x) + φ x * (gψ n x - g x) ∂μ := by
                  congr with x
                  ring
          _ = (∫ x, g x * φ x ∂μ) + ∫ x, φ x * (gψ n x - g x) ∂μ :=
                _root_.MeasureTheory.integral_add hgi hdi
      linarith
    have h_aux :
        _root_.Filter.Tendsto
          (fun n => -(∫ x, g x * φ x ∂μ) - ∫ x, φ x * (gψ n x - g x) ∂μ)
          atTop (nhds (-(∫ x, g x * φ x ∂μ) - 0)) :=
      Tendsto.const_sub _ h_grad_int
    simpa [μ, h_eq] using h_aux
  have h_eq_n :
      ∀ n, ∫ x in Ω, ψ n x * dφ x = -∫ x in Ω, gψ n x * φ x := by
    intro n
    exact hψ_wd n φ hφ hφ_supp hφ_sub
  have h_eq_tendsto :
      _root_.Filter.Tendsto (fun n => ∫ x in Ω, ψ n x * dφ x)
        atTop (nhds (-∫ x in Ω, g x * φ x)) := by
    simpa [h_eq_n] using h_rhs_tendsto
  exact tendsto_nhds_unique h_lhs_tendsto h_eq_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.HasWeakPartialDeriv.of_eLpNormApprox then
    throwError "Refusing to shadow existing declaration DeGiorgi.HasWeakPartialDeriv.of_eLpNormApprox"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.HasWeakPartialDeriv.of_eLpNormApprox ``Submission.DeGiorgi.HasWeakPartialDeriv.of_eLpNormApprox

/-! ## Indicator-Difference Convergence -/

theorem exists_subseq_tendsto_ae_of_tendsto_eLpNorm
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α} {f : α → ℝ} {ψ : ℕ → α → ℝ}
    (hψ_aemeas : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (ψ n) μ)
    (hf_aemeas : _root_.MeasureTheory.AEStronglyMeasurable f μ)
    (hψ :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - f x) 2 μ) _root_.Filter.atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => ψ (ns n) x) _root_.Filter.atTop (nhds (f x)) := by
  have htim : _root_.MeasureTheory.TendstoInMeasure μ ψ _root_.Filter.atTop f := by
    exact MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) hψ_aemeas hf_aemeas hψ
  exact htim.exists_seq_tendsto_ae

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.exists_subseq_tendsto_ae_of_tendsto_eLpNorm then
    throwError "Refusing to shadow existing declaration DeGiorgi.exists_subseq_tendsto_ae_of_tendsto_eLpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.exists_subseq_tendsto_ae_of_tendsto_eLpNorm ``Submission.DeGiorgi.exists_subseq_tendsto_ae_of_tendsto_eLpNorm

private lemma indicator_diff_mul_le_abs {a c d : ℝ} :
    |(if 0 < a then d else 0) - (if 0 < c then d else 0)| ≤ |d| := by
  by_cases ha : 0 < a <;> by_cases hc : 0 < c <;> simp [ha, hc]

run_cmd do
  let target := ``Submission.DeGiorgi.indicator_diff_mul_le_abs
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.indicator_diff_mul_le_abs target :: scope.openDecls } }

private lemma tendsto_indicator_diff_mul_zero_of_tendsto
    {a : ℕ → ℝ} {u g : ℝ}
    (ha : _root_.Filter.Tendsto a _root_.Filter.atTop (nhds u)) (hg0 : u = 0 → g = 0) :
    _root_.Filter.Tendsto (fun n => (if 0 < a n then g else 0) - (if 0 < u then g else 0))
      atTop (nhds 0) := by
  by_cases hu0 : u = 0
  · have hg : g = 0 := hg0 hu0
    simp [hu0, hg]
  by_cases hu : 0 < u
  · have hpos : ∀ᶠ n in _root_.Filter.atTop, 0 < a n := by
      have hnhds : {y : ℝ | u / 2 < y} ∈ 𝓝 u := Ioi_mem_nhds (by linarith)
      filter_upwards [ha hnhds] with n hn
      have hu_half : 0 < u / 2 := by linarith
      exact lt_trans hu_half hn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with n hn
    simp [hn, hu]
  · have hu_neg : u < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hu) (by simpa using hu0)
    have hneg : ∀ᶠ n in _root_.Filter.atTop, a n < u / 2 := by
      have hnhds : {y : ℝ | y < u / 2} ∈ 𝓝 u := Iio_mem_nhds (by linarith)
      filter_upwards [ha hnhds] with n hn
      exact hn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hneg] with n hn
    have hna : ¬ 0 < a n := by linarith
    simp [hna, hu]

run_cmd do
  let target := ``Submission.DeGiorgi.tendsto_indicator_diff_mul_zero_of_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.tendsto_indicator_diff_mul_zero_of_tendsto target :: scope.openDecls } }

/-
Indicator-convergence theorem for the positive-part chain rule.
-/
omit [NeZero d] in
theorem tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
    {μ : _root_.MeasureTheory.Measure E} {u G : E → ℝ} {ψ : ℕ → E → ℝ}
    (hψ_aestrong : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (ψ n) μ)
    (hu_aestrong : _root_.MeasureTheory.AEStronglyMeasurable u μ)
    (hG_memLp : _root_.MeasureTheory.MemLp G 2 μ)
    (hzero : ∀ᵐ x ∂μ, u x = 0 → G x = 0)
    (hψ :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) 2 μ) _root_.Filter.atTop (nhds 0)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
      (if 0 < ψ n x then G x else 0) -
        (if 0 < u x then G x else 0))
      2 μ) _root_.Filter.atTop (nhds 0) := by
  let F : ℕ → E → ℝ := fun n x =>
    (if 0 < ψ n x then G x else 0) - (if 0 < u x then G x else 0)
  have hF_meas : ∀ n, _root_.MeasureTheory.AEStronglyMeasurable (F n) μ := by
    intro n
    have hψ_pos : _root_.MeasureTheory.NullMeasurableSet {x | 0 < ψ n x} μ := by
      exact AEStronglyMeasurable.nullMeasurableSet_lt
        (μ := μ) stronglyMeasurable_const.aestronglyMeasurable (hψ_aestrong n)
    have hu_pos : _root_.MeasureTheory.NullMeasurableSet {x | 0 < u x} μ := by
      exact AEStronglyMeasurable.nullMeasurableSet_lt
        (μ := μ) stronglyMeasurable_const.aestronglyMeasurable hu_aestrong
    let h : _root_.MeasureTheory.AEStronglyMeasurable (F n) μ :=
      (hG_memLp.aestronglyMeasurable.indicator₀ hψ_pos).sub
        (hG_memLp.aestronglyMeasurable.indicator₀ hu_pos)
    exact h
  have hF_dom : ∀ n x, ‖F n x‖ ≤ ‖G x‖ := by
    intro n x
    exact indicator_diff_mul_le_abs (a := ψ n x) (c := u x) (d := G x)
  have huiG : _root_.MeasureTheory.UnifIntegrable (fun _ : ℕ => G) 2 μ := by
    exact MeasureTheory.unifIntegrable_const (p := (2 : ℝ≥0∞))
      (by norm_num) (by simp) hG_memLp
  have huiF : _root_.MeasureTheory.UnifIntegrable F 2 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huiG hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    calc
      eLpNorm (s.indicator (F n)) 2 μ ≤ _root_.MeasureTheory.eLpNorm (s.indicator G) 2 μ := by
        refine _root_.MeasureTheory.eLpNorm_mono ?_
        intro x
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs]
          exact hF_dom n x
        · simp [Set.indicator_of_notMem, hx]
      _ ≤ ENNReal.ofReal ε := hδ' 0 s hs hμs
  have hutG : _root_.MeasureTheory.UnifTight (fun _ : ℕ => G) 2 μ := by
    exact MeasureTheory.unifTight_const (p := (2 : ℝ≥0∞)) (by simp) hG_memLp
  have hutF : _root_.MeasureTheory.UnifTight F 2 μ := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := hutG hε
    refine ⟨s, hμs, fun n => ?_⟩
    calc
      eLpNorm (sᶜ.indicator (F n)) 2 μ ≤ _root_.MeasureTheory.eLpNorm (sᶜ.indicator G) 2 μ := by
        refine _root_.MeasureTheory.eLpNorm_mono ?_
        intro x
        by_cases hx : x ∈ sᶜ
        · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs]
          exact hF_dom n x
        · simp [Set.indicator_of_notMem, hx]
      _ ≤ ε := hs' 0
  refine _root_.Filter.tendsto_of_subseq_tendsto ?_
  intro ns hns
  obtain ⟨ms, -, hms_ae⟩ :=
    exists_subseq_tendsto_ae_of_tendsto_eLpNorm
      (μ := μ) (f := u) (ψ := fun n => ψ (ns n))
      (fun n => hψ_aestrong (ns n)) hu_aestrong (hψ.comp hns)
  have hui_subseq : _root_.MeasureTheory.UnifIntegrable (fun n => F (ns (ms n))) 2 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := huiF hε
    exact ⟨δ, hδ, fun n s hs hμs => hδ' (ns (ms n)) s hs hμs⟩
  have hut_subseq : _root_.MeasureTheory.UnifTight (fun n => F (ns (ms n))) 2 μ := by
    intro ε hε
    obtain ⟨s, hμs, hs'⟩ := hutF hε
    exact ⟨s, hμs, fun n => hs' (ns (ms n))⟩
  have hF_ae :
      ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun n => F (ns (ms n)) x) _root_.Filter.atTop (nhds 0) := by
    filter_upwards [hzero, hms_ae] with x hxzero hxt
    simpa [F] using
      tendsto_indicator_diff_mul_zero_of_tendsto
        (a := fun n => ψ (ns (ms n)) x) (u := u x) (g := G x) hxt hxzero
  refine ⟨ms, ?_⟩
  have hLpF :
      Tendsto (fun n => _root_.MeasureTheory.eLpNorm (F (ns (ms n))) 2 μ) _root_.Filter.atTop (nhds 0) := by
    have hLpF0 :
        Tendsto (fun n => _root_.MeasureTheory.eLpNorm (F (ns (ms n)) - fun _ => (0 : ℝ)) 2 μ) _root_.Filter.atTop (nhds 0) := by
      exact
        (MeasureTheory.tendsto_Lp_of_tendsto_ae (μ := μ) (p := (2 : ℝ≥0∞))
          (hp := by norm_num) (hp' := by simp)
          (haef := fun n => hF_meas (ns (ms n)))
          (hg' := (MeasureTheory.MemLp.zero' (p := (2 : ℝ≥0∞)) (μ := μ)))
          hui_subseq hut_subseq hF_ae)
    have hEq0 :
        (fun n => _root_.MeasureTheory.eLpNorm (F (ns (ms n)) - fun _ => (0 : ℝ)) 2 μ) =
          (fun n => _root_.MeasureTheory.eLpNorm (F (ns (ms n))) 2 μ) := by
      funext n
      congr 1
      ext x
      simp
    rw [hEq0] at hLpF0
    exact hLpF0
  simpa [F] using hLpF

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm then
    throwError "Refusing to shadow existing declaration DeGiorgi.tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm ``Submission.DeGiorgi.tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm

/-! ## Positive-Part Chain Rule -/

omit [NeZero d] in
private lemma support_positivePart_subset_support (f : E → ℝ) :
    Function.support (fun x => _root_.Max.max (f x) 0) ⊆ Function.support f := by
  intro x hx
  by_contra hfx
  have hfx0 : f x = 0 := by
    simpa [Function.support] using hfx
  have : _root_.Max.max (f x) 0 = 0 := by
    simp [hfx0]
  exact hx this

run_cmd do
  let target := ``Submission.DeGiorgi.support_positivePart_subset_support
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.support_positivePart_subset_support target :: scope.openDecls } }

omit [NeZero d] in
private lemma hasCompactSupport_positivePart {f : E → ℝ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun x => _root_.Max.max (f x) 0) :=
  hf.mono (support_positivePart_subset_support f)

run_cmd do
  let target := ``Submission.DeGiorgi.hasCompactSupport_positivePart
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.hasCompactSupport_positivePart target :: scope.openDecls } }

omit [NeZero d] in
private lemma lineDeriv_positivePart_eq_of_contDiff
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x v : E) :
    lineDeriv ℝ (fun y => _root_.Max.max (f y) 0) x v =
      if 0 < f x then fderiv ℝ f x v else 0 := by
  have hfdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  by_cases hx : 0 < f x
  · have hEq : (fun y => _root_.Max.max (f y) 0) =ᶠ[𝓝 x] f := by
      have hpos : ∀ᶠ y in nhds x, 0 < f y :=
        (isOpen_lt continuous_const hf.continuous).mem_nhds hx
      filter_upwards [hpos] with y hy
      simp [max_eq_left hy.le]
    rw [hEq.lineDeriv_eq]
    simpa [hx] using (hfdiff x).lineDeriv_eq_fderiv (v := v)
  · have hx_nonpos : f x ≤ 0 := le_of_not_gt hx
    by_cases hx_zero : f x = 0
    · have hmin : IsLocalMin (fun y => _root_.Max.max (f y) 0) x := by
        change ∀ᶠ y in nhds x, _root_.Max.max (f x) 0 ≤ _root_.Max.max (f y) 0
        filter_upwards [] with y
        simp [hx_zero]
      have hzero : lineDeriv ℝ (fun y => _root_.Max.max (f y) 0) x v = 0 := by
        simpa using congrFun hmin.lineDeriv_eq_zero v
      simp [hx, hzero]
    · have hx_neg : f x < 0 := lt_of_le_of_ne hx_nonpos hx_zero
      have hEq : (fun y => _root_.Max.max (f y) 0) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        have hneg : ∀ᶠ y in nhds x, f y < 0 :=
          (isOpen_lt hf.continuous continuous_const).mem_nhds hx_neg
        filter_upwards [hneg] with y hy
        simp [max_eq_right hy.le]
      rw [hEq.lineDeriv_eq]
      have hconst : lineDeriv ℝ (fun _ : E => (0 : ℝ)) x v = 0 := by
        simpa using ((hasFDerivAt_const (0 : ℝ) x).hasLineDerivAt v).lineDeriv
      simp [hx, hconst]

run_cmd do
  let target := ``Submission.DeGiorgi.lineDeriv_positivePart_eq_of_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.lineDeriv_positivePart_eq_of_contDiff target :: scope.openDecls } }

omit [NeZero d] in
private theorem weakPartialDeriv_positivePart_of_contDiff
    {Ω : Set E} {i : Fin d} {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hf_supp : HasCompactSupport f) :
    HasWeakPartialDeriv i
      (fun x => if 0 < f x then fderiv ℝ f x (EuclideanSpace.single i 1) else 0)
      (fun x => _root_.Max.max (f x) 0) Ω := by
  intro φ hφ hφ_supp hφ_sub
  obtain ⟨Cf, hLip_f⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hf_supp hf one_ne_zero
  obtain ⟨Cφ, hLip_φ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ_supp hφ (by simp)
  have hLip_pos : LipschitzWith Cf (fun y => _root_.Max.max (f y) 0) := by
    have hcomp := MeasureTheory.Lp.lipschitzWith_pos_part.comp hLip_f
    have hcomp' : LipschitzWith Cf ((fun y : ℝ => _root_.Max.max y 0) ∘ f) := by
      simpa only [one_mul] using hcomp
    let h : LipschitzWith Cf (fun y => _root_.Max.max (f y) 0) :=
      hcomp'
    exact h
  let ei : E := EuclideanSpace.single i (1 : ℝ)
  have hLineDeriv_f :
      ∀ x, lineDeriv ℝ (fun y => _root_.Max.max (f y) 0) x ei =
        if 0 < f x then fderiv ℝ f x ei else 0 :=
    fun x => lineDeriv_positivePart_eq_of_contDiff hf x ei
  have hLineDeriv_φ :
      ∀ x, lineDeriv ℝ φ x (-ei) = -fderiv ℝ φ x ei := by
    intro x
    rw [(hφ.differentiable (by simp) x).lineDeriv_eq_fderiv]
    simp [ei]
  have hDeriv_φ_sub : tsupport (fun x => fderiv ℝ φ x ei) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ ei).trans hφ_sub
  have hIBP :=
    LipschitzWith.integral_lineDeriv_mul_eq
      (μ := _root_.MeasureTheory.MeasureSpace.volume) hLip_pos hLip_φ hφ_supp ei
  simp_rw [hLineDeriv_f, hLineDeriv_φ] at hIBP
  have hLHS_zero :
      ∀ x, x ∉ Ω →
        (if 0 < f x then fderiv ℝ f x ei else 0) * φ x = 0 := by
    intro x hx
    have hφx : φ x = 0 := by
      by_contra hφx
      exact hx (hφ_sub (subset_tsupport _ hφx))
    simp [hφx]
  have hRHS_zero :
      ∀ x, x ∉ Ω → (-fderiv ℝ φ x ei) * _root_.Max.max (f x) 0 = 0 := by
    intro x hx
    have hderivx : fderiv ℝ φ x ei = 0 := by
      by_contra hderivx
      exact hx (hDeriv_φ_sub (subset_tsupport _ hderivx))
    rw [hderivx, neg_zero, _root_.MulZeroClass.zero_mul]
  rw [← _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hLHS_zero,
      ← _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hRHS_zero] at hIBP
  have hIBP' :
      ∫ x in Ω, (if 0 < f x then fderiv ℝ f x ei else 0) * φ x =
        -∫ x in Ω, _root_.Max.max (f x) 0 * fderiv ℝ φ x ei := by
    rw [show (∫ x in Ω, -fderiv ℝ φ x ei * _root_.Max.max (f x) 0) =
        -∫ x in Ω, _root_.Max.max (f x) 0 * fderiv ℝ φ x ei by
        simp_rw [neg_mul, mul_comm]
        rw [_root_.MeasureTheory.integral_neg]] at hIBP
    exact hIBP
  have hneg := congrArg Neg.neg hIBP'
  simpa [neg_neg, ei] using hneg.symm

run_cmd do
  let target := ``Submission.DeGiorgi.weakPartialDeriv_positivePart_of_contDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.weakPartialDeriv_positivePart_of_contDiff target :: scope.openDecls } }

omit [NeZero d] in
private lemma positivePart_sub_abs_le {f g : E → ℝ} (x : E) :
    |max (f x) 0 - _root_.Max.max (g x) 0| ≤ |f x - g x| := by
  have h := MeasureTheory.Lp.lipschitzWith_pos_part.dist_le_mul (f x) (g x)
  simpa [dist_eq_norm, Real.norm_eq_abs, mul_comm] using h

run_cmd do
  let target := ``Submission.DeGiorgi.positivePart_sub_abs_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.positivePart_sub_abs_le target :: scope.openDecls } }

omit [NeZero d] in
private theorem eLpNorm_positivePart_sub_le
    {f g : E → ℝ} {μ : _root_.MeasureTheory.Measure E} :
    _root_.MeasureTheory.eLpNorm (fun x => _root_.Max.max (f x) 0 - _root_.Max.max (g x) 0) 2 μ ≤
      eLpNorm (fun x => f x - g x) 2 μ := by
  exact _root_.MeasureTheory.eLpNorm_mono_ae (Eventually.of_forall (positivePart_sub_abs_le (f := f) (g := g)))

run_cmd do
  let target := ``Submission.DeGiorgi.eLpNorm_positivePart_sub_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.eLpNorm_positivePart_sub_le target :: scope.openDecls } }

omit [NeZero d] in
private theorem tendsto_eLpNorm_positivePart_sub
    {f : E → ℝ} {g : ℕ → E → ℝ} {μ : _root_.MeasureTheory.Measure E}
    (h :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => g n x - f x) 2 μ) _root_.Filter.atTop (nhds 0)) :
    _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => _root_.Max.max (g n x) 0 - _root_.Max.max (f x) 0) 2 μ)
      atTop (nhds 0) := by
  have hbound :
      ∀ n, _root_.MeasureTheory.eLpNorm (fun x => _root_.Max.max (g n x) 0 - _root_.Max.max (f x) 0) 2 μ ≤
        eLpNorm (fun x => g n x - f x) 2 μ := by
    intro n
    exact eLpNorm_positivePart_sub_le (f := fun x => g n x) (g := fun x => f x)
  have hnonneg :
      ∀ n, 0 ≤ _root_.MeasureTheory.eLpNorm (fun x => _root_.Max.max (g n x) 0 - _root_.Max.max (f x) 0) 2 μ := by
    intro n
    positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h hnonneg hbound

run_cmd do
  let target := ``Submission.DeGiorgi.tendsto_eLpNorm_positivePart_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.tendsto_eLpNorm_positivePart_sub target :: scope.openDecls } }

/-- Auxiliary positive-part witness constructor: this is the transportable core
assuming the zero-set vanishing input and the smooth approximation data are
already available. -/
noncomputable def MemW1pWitness.posPartOfAux
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (hzero :
      ∀ i : Fin d, ∀ᵐ x ∂(volume.restrict Ω), u x = 0 → hw.weakGrad x i = 0)
    (happrox :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0) ∧
        (∀ i : Fin d,
          _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0))) :
    MemW1pWitness 2 (fun x => _root_.Max.max (u x) 0) Ω := by
  let _ := (inferInstance : (MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Ω)))
  let ψ : ℕ → E → ℝ := Classical.choose happrox
  have hψspec := Classical.choose_spec happrox
  have hψ_smooth : ∀ n, ContDiff ℝ 1 (ψ n) := hψspec.1
  have hψspec' := hψspec.2
  have hψ_cpt : ∀ n, HasCompactSupport (ψ n) := hψspec'.1
  have hψspec'' := hψspec'.2
  have hψ_func :
      _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict Ω))
        atTop (nhds 0) := hψspec''.1
  have hψ_grad :
      ∀ i : Fin d,
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
          (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω))
        atTop (nhds 0) := hψspec''.2
  refine
    { memLp := by
        simpa using hw.memLp.pos_part
      weakGrad := fun x => if 0 < u x then hw.weakGrad x else 0
      weakGrad_component_memLp := ?_
      isWeakGrad := ?_ }
  · intro i
    simpa using posPartGrad_component_memLp hw i
  · intro i
    let μ : _root_.MeasureTheory.Measure E := volume.restrict Ω
    let g : E → ℝ := fun x => if 0 < u x then hw.weakGrad x i else 0
    let gψ : ℕ → E → ℝ := fun n x =>
      if 0 < ψ n x then (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) else 0
    have hg_memLp : _root_.MeasureTheory.MemLp g 2 μ := by
      exact indicator_component_memLp hw.memLp.aemeasurable (hw.weakGrad_component_memLp i)
    have hψ_wd : ∀ n, HasWeakPartialDeriv i (gψ n) (fun x => _root_.Max.max (ψ n x) 0) Ω := by
      intro n
      simpa [gψ] using
        weakPartialDeriv_positivePart_of_contDiff (Ω := Ω) (i := i) (hψ_smooth n) (hψ_cpt n)
    have hψ_fun_memLp : ∀ n, _root_.MeasureTheory.MemLp (fun x => _root_.Max.max (ψ n x) 0 - _root_.Max.max (u x) 0) 2 μ := by
      intro n
      have hfirst : _root_.MeasureTheory.MemLp (fun x => _root_.Max.max (ψ n x) 0) 2 μ := by
        exact (((hψ_smooth n).continuous.max continuous_const).memLp_of_hasCompactSupport
          (hasCompactSupport_positivePart (hψ_cpt n))).restrict Ω
      exact hfirst.sub (by simpa using hw.memLp.pos_part)
    have hψ_fun :
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => _root_.Max.max (ψ n x) 0 - _root_.Max.max (u x) 0) 2 μ)
          atTop (nhds 0) :=
      tendsto_eLpNorm_positivePart_sub hψ_func
    have hψ_grad_memLp : ∀ n, _root_.MeasureTheory.MemLp (fun x => gψ n x - g x) 2 μ := by
      intro n
      have hderiv_cont : Continuous
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
        ((hψ_smooth n).fderiv_right (m := 0) (by norm_cast)).continuous.clm_apply
          continuous_const
      have hderiv_cpt : HasCompactSupport
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
        (hψ_cpt n).fderiv_apply (𝕜 := ℝ) _
      have hderiv_memLp : _root_.MeasureTheory.MemLp
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) 2 μ :=
        (hderiv_cont.memLp_of_hasCompactSupport hderiv_cpt).restrict Ω
      have hfirst_raw : _root_.MeasureTheory.MemLp
          (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 μ :=
        hderiv_memLp.sub (hw.weakGrad_component_memLp i)
      have hψ_meas : AEMeasurable (ψ n) μ :=
        ((hψ_smooth n).continuous.aemeasurable.restrict)
      have hfirst : _root_.MeasureTheory.MemLp
          (fun x => if 0 < ψ n x then
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
          2 μ := indicator_component_memLp hψ_meas hfirst_raw
      have hsecond : _root_.MeasureTheory.MemLp
          (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x) 2 μ := by
        have hleft : _root_.MeasureTheory.MemLp (fun x => if 0 < ψ n x then hw.weakGrad x i else 0) 2 μ :=
          indicator_component_memLp hψ_meas (hw.weakGrad_component_memLp i)
        exact hleft.sub hg_memLp
      have hEq :
          (fun x => gψ n x - g x) =
            (fun x =>
              (if 0 < ψ n x then
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0) +
                ((if 0 < ψ n x then hw.weakGrad x i else 0) - g x)) := by
        funext x
        by_cases hxψ : 0 < ψ n x <;> by_cases hxu : 0 < u x <;> simp [gψ, g, hxψ, hxu]
      have hsum : _root_.MeasureTheory.MemLp
          (fun x =>
            (if 0 < ψ n x then
              (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0) +
              ((if 0 < ψ n x then hw.weakGrad x i else 0) - g x))
          2 μ := ⟨hfirst.aestronglyMeasurable.add hsecond.aestronglyMeasurable,
            _root_.MeasureTheory.eLpNorm_add_lt_top hfirst hsecond⟩
      simpa [hEq] using hsum
    have hψ_grad_tendsto :
        Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => gψ n x - g x) 2 μ) _root_.Filter.atTop (nhds 0) := by
      have hfirst :
          _root_.Filter.Tendsto
            (fun n => _root_.MeasureTheory.eLpNorm
              (fun x => if 0 < ψ n x then
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
              2 μ) _root_.Filter.atTop (nhds 0) := by
        have hbound :
            ∀ n,
              _root_.MeasureTheory.eLpNorm
                (fun x => if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
                2 μ
              ≤ _root_.MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
                  2 μ := by
          intro n
          refine _root_.MeasureTheory.eLpNorm_mono ?_
          intro x
          by_cases hx : 0 < ψ n x <;> simp [hx]
        have hnonneg :
            ∀ n,
              0 ≤ _root_.MeasureTheory.eLpNorm
                (fun x => if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
                2 μ := by
          intro n
          positivity
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds (hψ_grad i) hnonneg hbound
      have hsecond :
          _root_.Filter.Tendsto
            (fun n => _root_.MeasureTheory.eLpNorm
              (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
              2 μ) _root_.Filter.atTop (nhds 0) := by
        simpa [g] using
          tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
            (μ := μ) (u := u) (G := fun x => hw.weakGrad x i) (ψ := ψ)
            (hψ_aestrong := fun n => (hψ_smooth n).continuous.aestronglyMeasurable.restrict)
            (hu_aestrong := hw.memLp.aestronglyMeasurable)
            (hG_memLp := hw.weakGrad_component_memLp i)
            (hzero := hzero i)
            (hψ := hψ_func)
      have hbound :
          ∀ n, _root_.MeasureTheory.eLpNorm (fun x => gψ n x - g x) 2 μ ≤
            _root_.MeasureTheory.eLpNorm
              (fun x => if 0 < ψ n x then
                (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
              2 μ
            +
            _root_.MeasureTheory.eLpNorm
              (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
              2 μ := by
        intro n
        have hψ_meas : AEMeasurable (ψ n) μ :=
          ((hψ_smooth n).continuous.aemeasurable.restrict)
        have hderiv_cont : Continuous
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
          ((hψ_smooth n).fderiv_right (m := 0) (by norm_cast)).continuous.clm_apply
            continuous_const
        have hderiv_cpt : HasCompactSupport
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) :=
          (hψ_cpt n).fderiv_apply (𝕜 := ℝ) _
        have hderiv_memLp : _root_.MeasureTheory.MemLp
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1)) 2 μ :=
          (hderiv_cont.memLp_of_hasCompactSupport hderiv_cpt).restrict Ω
        have hfirst_raw : _root_.MeasureTheory.MemLp
            (fun x => (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 μ :=
          hderiv_memLp.sub (hw.weakGrad_component_memLp i)
        have hfirst_mem : _root_.MeasureTheory.MemLp
            (fun x => if 0 < ψ n x then
              (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
            2 μ := indicator_component_memLp hψ_meas hfirst_raw
        have hsecond_mem : _root_.MeasureTheory.MemLp
            (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
            2 μ := by
          exact (indicator_component_memLp hψ_meas (hw.weakGrad_component_memLp i)).sub hg_memLp
        have hEq :
            (fun x => gψ n x - g x) =
              (fun x =>
                (if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0) +
                  ((if 0 < ψ n x then hw.weakGrad x i else 0) - g x)) := by
          funext x
          by_cases hxψ : 0 < ψ n x <;> by_cases hxu : 0 < u x <;> simp [gψ, g, hxψ, hxu]
        rw [hEq]
        exact _root_.MeasureTheory.eLpNorm_add_le
          hfirst_mem.aestronglyMeasurable
          hsecond_mem.aestronglyMeasurable
          (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hnonneg : ∀ n, 0 ≤ _root_.MeasureTheory.eLpNorm (fun x => gψ n x - g x) 2 μ := by
        intro n
        positivity
      have hupper :
          _root_.Filter.Tendsto
            (fun n =>
              _root_.MeasureTheory.eLpNorm
                (fun x => if 0 < ψ n x then
                  (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i else 0)
                2 μ
              +
              _root_.MeasureTheory.eLpNorm
                (fun x => (if 0 < ψ n x then hw.weakGrad x i else 0) - g x)
                2 μ)
            atTop (nhds 0) := by
        simpa using hfirst.add hsecond
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hnonneg hbound
    have hg_eq :
        (fun x => ((if 0 < u x then hw.weakGrad x else 0 : E) i)) = g := by
      funext x
      by_cases hx : 0 < u x <;> simp [g, hx]
    rw [hg_eq]
    exact
      HasWeakPartialDeriv.of_eLpNormApprox (d := d) hΩ
        (i := i) (f := fun x => _root_.Max.max (u x) 0) (g := g)
        (ψ := fun n x => _root_.Max.max (ψ n x) 0) (gψ := gψ)
        (by simpa using hw.memLp.pos_part)
        hg_memLp
        hψ_wd
        hψ_fun_memLp
        hψ_fun
        hψ_grad_memLp
        hψ_grad_tendsto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.posPartOfAux then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.posPartOfAux"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.posPartOfAux ``Submission.DeGiorgi.MemW1pWitness.posPartOfAux

/-- Positive-part witness constructor with the Stampacchia zero-set input
supplied automatically from the imported Chapter 02 theorem. The remaining
explicit hypothesis is just the smooth approximation package. -/
noncomputable def MemW1pWitness.posPart
    {Ω : Set E} [_root_.MeasureTheory.IsFiniteMeasure (volume.restrict Ω)]
    (hΩ : IsOpen Ω) {u : E → ℝ}
    (hw : MemW1pWitness 2 u Ω)
    (happrox :
      ∃ ψ : ℕ → E → ℝ,
        (∀ n, ContDiff ℝ 1 (ψ n)) ∧
        (∀ n, HasCompactSupport (ψ n)) ∧
        _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0) ∧
        (∀ i : Fin d,
          _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (fun x =>
            (fderiv ℝ (ψ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i)
            2 (volume.restrict Ω))
          _root_.Filter.atTop (nhds 0))) :
    MemW1pWitness 2 (fun x => _root_.Max.max (u x) 0) Ω :=
  MemW1pWitness.posPartOfAux hΩ hw
    (hw.weakGrad_ae_eq_zero_on_zeroSet hΩ) happrox

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.posPart then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.posPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.posPart ``Submission.DeGiorgi.MemW1pWitness.posPart

end DeGiorgi
