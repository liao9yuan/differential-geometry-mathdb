import Submission.DifferentialGeometry.External.DeGiorgi.WeakFormulation.SmoothTests

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Weak Divergence Pairings

This module assembles componentwise weak partial derivatives into a weak
divergence and extends the resulting divergence pairing from smooth compactly
supported tests to `H₀¹` tests.
-/

noncomputable section

open _root_.MeasureTheory _root_.Filter
open scoped _root_.InnerProductSpace

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

omit [NeZero d] in
/-- Componentwise weak partial derivatives assemble into the weak divergence
of a vector field. -/
theorem hasWeakDiv_sum_of_hasWeakPartialDeriv
    {Ω : Set E} {F : E → E} {G : Fin d → E → ℝ}
    (hF_loc : ∀ i : Fin d,
      _root_.MeasureTheory.LocallyIntegrable (fun x => F x i) (volume.restrict Ω))
    (hG_loc : ∀ i : Fin d, _root_.MeasureTheory.LocallyIntegrable (G i) (volume.restrict Ω))
    (hparts : ∀ i : Fin d,
      HasWeakPartialDeriv i (G i) (fun x => F x i) Ω) :
    HasWeakDiv (fun x => ∑ i : Fin d, G i x) F Ω := by
  intro φ hφ hφ_cpt hφ_sub
  have hleft_int : ∀ i : Fin d,
      _root_.MeasureTheory.Integrable (fun x => F x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
    intro i
    have hderiv_cont :
        Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hderiv_cpt :
        HasCompactSupport (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
      hφ_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hint :=
      (hF_loc i).integrable_smul_left_of_hasCompactSupport hderiv_cont hderiv_cpt
    simpa [smul_eq_mul, mul_comm] using hint
  have hright_int : ∀ i : Fin d,
      Integrable (fun x => G i x * φ x) (volume.restrict Ω) := by
    intro i
    have hint :=
      (hG_loc i).integrable_smul_left_of_hasCompactSupport hφ.continuous hφ_cpt
    simpa [smul_eq_mul, mul_comm] using hint
  calc
    ∫ x in Ω, ∑ i : Fin d,
        F x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        ∑ i : Fin d, ∫ x in Ω,
          F x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            rw [_root_.MeasureTheory.integral_finsetSum]
            exact fun i _hi => hleft_int i
    _ = ∑ i : Fin d, -(∫ x in Ω, G i x * φ x) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact hparts i φ hφ hφ_cpt hφ_sub
    _ = -(∑ i : Fin d, ∫ x in Ω, G i x * φ x) := by
          rw [Finset.sum_neg_distrib]
    _ = -(∫ x in Ω, ∑ i : Fin d, G i x * φ x) := by
          rw [_root_.MeasureTheory.integral_finsetSum]
          exact fun i _hi => hright_int i
    _ = -(∫ x in Ω, (∑ i : Fin d, G i x) * φ x) := by
          simp only [Finset.sum_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.hasWeakDiv_sum_of_hasWeakPartialDeriv then
    throwError "Refusing to shadow existing declaration DeGiorgi.hasWeakDiv_sum_of_hasWeakPartialDeriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.hasWeakDiv_sum_of_hasWeakPartialDeriv ``Submission.DeGiorgi.hasWeakDiv_sum_of_hasWeakPartialDeriv

omit [NeZero d] in
private lemma integral_mul_tendsto_zero
    {μ : _root_.MeasureTheory.Measure E} {f : E → ℝ} {g : ℕ → E → ℝ}
    (hf : _root_.MeasureTheory.MemLp f 2 μ)
    (hg : ∀ n, _root_.MeasureTheory.MemLp (g n) 2 μ)
    (hlim : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.eLpNorm (g n) 2 μ) _root_.Filter.atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) _root_.Filter.atTop (nhds 0) := by
  have hpq : (2 : ℝ).HolderConjugate (2 : ℝ) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  let C : ℝ := _root_.MeasureTheory.lpNorm f 2 μ
  have hlim' : _root_.Filter.Tendsto (fun n => _root_.MeasureTheory.lpNorm (g n) 2 μ) _root_.Filter.atTop (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (_root_.MeasureTheory.eLpNorm (g n) 2 μ).toReal) _root_.Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (_root_.MeasureTheory.eLpNorm (g n) 2 μ).toReal) = fun n => _root_.MeasureTheory.lpNorm (g n) 2 μ := by
      funext n
      simpa using
        (_root_.MeasureTheory.toReal_eLpNorm (μ := μ) (p := (2 : ENNReal)) (f := g n)
          (hg n).aestronglyMeasurable)
    rw [← hEq]
    exact hlim_toReal
  have hbound : ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * _root_.MeasureTheory.lpNorm (g n) 2 μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using _root_.MeasureTheory.norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have hf' : _root_.MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
    have hg' : _root_.MeasureTheory.MemLp (g n) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg n
    have hholder :=
      _root_.MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := (2 : ℝ)) (q := (2 : ℝ)) hpq hf' hg'
    have h_f_lp :
        lpNorm f 2 μ = (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
      simpa using
        (_root_.MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := (2 : ENNReal)) (f := f) (by norm_num) (by simp)
          hf.aestronglyMeasurable)
    have h_g_lp :
        lpNorm (g n) 2 μ = (∫ x, ‖g n x‖ ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹) := by
      simpa using
        (_root_.MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := (2 : ENNReal)) (f := g n) (by norm_num) (by simp)
          (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * _root_.MeasureTheory.lpNorm (g n) 2 μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using hholder
  have hupper : _root_.Filter.Tendsto (fun n => C * _root_.MeasureTheory.lpNorm (g n) 2 μ) _root_.Filter.atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have habs : _root_.Filter.Tendsto (fun n => |∫ x, f x * g n x ∂μ|) _root_.Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound hupper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

run_cmd do
  let target := ``Submission.DeGiorgi.integral_mul_tendsto_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DeGiorgi.integral_mul_tendsto_zero target :: scope.openDecls } }

omit [NeZero d] in
/-- A square-integrable weak divergence evaluates the divergence-form RHS on
an `H₀¹` test as its scalar `L²` pairing with that test. -/
theorem weakProblemRHSOfField_eq_integral
    {Ω : Set E} (hΩ : IsOpen Ω)
    {F : E → E} (hF : _root_.MeasureTheory.MemLp F 2 (volume.restrict Ω))
    {g : E → ℝ} (hg : _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω))
    (hdiv : HasWeakDiv g F Ω)
    {v : E → ℝ} (hv0 : MemH01 v Ω) :
    weakProblemRHSOfField (Ω := Ω) F v = ∫ x in Ω, g x * v x := by
  let μ : _root_.MeasureTheory.Measure E := volume.restrict Ω
  rcases hv0.2 with ⟨hw, φ, hφ_smooth, hφ_cpt, hφ_sub, hφ_fun, hφ_grad⟩
  let hφtest : ∀ n : ℕ, IsSmoothTestOn Ω (φ n) := fun n =>
    ⟨hφ_smooth n, hφ_cpt n, hφ_sub n⟩
  let hφw : ∀ n : ℕ, MemW1pWitness 2 (φ n) Ω := fun n =>
    smoothTestWitness hΩ (hφtest n)
  have hF_comp : ∀ i : Fin d, _root_.MeasureTheory.MemLp (fun x => F x i) 2 μ := by
    intro i
    have hF_ofLp :
        AEStronglyMeasurable (fun x => (WithLp.ofLp (F x) : Fin d → ℝ)) μ :=
      (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp_aestronglyMeasurable
        hF.aestronglyMeasurable
    have hmeas : _root_.MeasureTheory.AEStronglyMeasurable (fun x => F x i) μ := by
      simpa using (continuous_apply i).comp_aestronglyMeasurable hF_ofLp
    refine hF.of_le hmeas ?_
    filter_upwards with x
    simpa using PiLp.norm_apply_le (p := (2 : ENNReal)) (x := F x) (i := i)
  have hfun_mem : ∀ n, _root_.MeasureTheory.MemLp (fun x => φ n x - v x) 2 μ := by
    intro n
    exact (hφw n).memLp.sub hw.memLp
  have hφgrad_mem : ∀ n, ∀ i : Fin d,
      MemLp (fun x => (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1)) 2 μ := by
    intro n i
    simpa [hφw, smoothTestWitness, smoothGradField, PiLp.toLp_apply] using
      (hφw n).weakGrad_component_memLp i
  have hgrad_mem : ∀ n, ∀ i : Fin d,
      _root_.MeasureTheory.MemLp (fun x =>
        (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) 2 μ := by
    intro n i
    exact MemLp.ae_eq (Filter.Eventually.of_forall fun x => by
      simp only [hφw, smoothTestWitness, smoothGradField, PiLp.toLp_apply,
        Pi.sub_apply]) <|
      ((hφw n).weakGrad_component_memLp i).sub (hw.weakGrad_component_memLp i)
  have hleft_i : ∀ i : Fin d,
      _root_.Filter.Tendsto
        (fun n => ∫ x,
          F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ)
        atTop (nhds (∫ x, F x i * hw.weakGrad x i ∂μ)) := by
    intro i
    have hzero := integral_mul_tendsto_zero (hF_comp i) (fun n => hgrad_mem n i) (hφ_grad i)
    have hEq : ∀ n,
        ∫ x, F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ =
          (∫ x, F x i * hw.weakGrad x i ∂μ) +
            ∫ x, F x i *
              ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) - hw.weakGrad x i) ∂μ := by
      intro n
      calc
        ∫ x, F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ =
            ∫ x, F x i * hw.weakGrad x i +
              F x i * ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
                hw.weakGrad x i) ∂μ := by
              apply _root_.MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
        _ = (∫ x, F x i * hw.weakGrad x i ∂μ) +
            ∫ x, F x i *
              ((fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) -
                hw.weakGrad x i) ∂μ := by
              simpa only [Pi.add_apply, Pi.mul_apply] using!
                _root_.MeasureTheory.integral_add
                  ((hF_comp i).integrable_mul (hw.weakGrad_component_memLp i))
                  ((hF_comp i).integrable_mul (hgrad_mem n i))
    simpa only [hEq, add_zero] using
      Tendsto.const_add (∫ x, F x i * hw.weakGrad x i ∂μ) hzero
  have hleft :
      _root_.Filter.Tendsto
        (fun n => ∫ x, ∑ i : Fin d,
          F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ)
        atTop (nhds (∫ x, ∑ i : Fin d, F x i * hw.weakGrad x i ∂μ)) := by
    have hsum :=
      tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _hi => hleft_i i)
    have hseq_int : ∀ n,
        ∫ x, ∑ i : Fin d,
            F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ =
          ∑ i : Fin d, ∫ x,
            F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ := by
      intro n
      rw [_root_.MeasureTheory.integral_finsetSum]
      exact fun i _hi => (hF_comp i).integrable_mul (hφgrad_mem n i)
    have hlim_int :
        ∫ x, ∑ i : Fin d, F x i * hw.weakGrad x i ∂μ =
          ∑ i : Fin d, ∫ x, F x i * hw.weakGrad x i ∂μ := by
      rw [_root_.MeasureTheory.integral_finsetSum]
      exact fun i _hi => (hF_comp i).integrable_mul (hw.weakGrad_component_memLp i)
    rw [hlim_int]
    exact hsum.congr' (Filter.Eventually.of_forall fun n => (hseq_int n).symm)
  have hright :
      Tendsto (fun n => ∫ x, g x * φ n x ∂μ) _root_.Filter.atTop (nhds (∫ x, g x * v x ∂μ)) := by
    have hzero := integral_mul_tendsto_zero hg hfun_mem hφ_fun
    have hEq : ∀ n,
        ∫ x, g x * φ n x ∂μ =
          (∫ x, g x * v x ∂μ) + ∫ x, g x * (φ n x - v x) ∂μ := by
      intro n
      calc
        ∫ x, g x * φ n x ∂μ =
            ∫ x, g x * v x + g x * (φ n x - v x) ∂μ := by
              apply _root_.MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
        _ = (∫ x, g x * v x ∂μ) + ∫ x, g x * (φ n x - v x) ∂μ := by
              simpa only [Pi.add_apply, Pi.mul_apply] using!
                _root_.MeasureTheory.integral_add (hg.integrable_mul hw.memLp)
                  (hg.integrable_mul (hfun_mem n))
    simpa only [hEq, add_zero] using Tendsto.const_add (∫ x, g x * v x ∂μ) hzero
  have hseq : ∀ n,
      -(∫ x, ∑ i : Fin d,
          F x i * (fderiv ℝ (φ n) x) (EuclideanSpace.single i 1) ∂μ) =
        ∫ x, g x * φ n x ∂μ := by
    intro n
    have hn := hdiv (φ n) (hφ_smooth n) (hφ_cpt n) (hφ_sub n)
    simpa [μ] using congrArg Neg.neg hn
  have hright_neg :
      _root_.Filter.Tendsto (fun n => ∫ x, g x * φ n x ∂μ) _root_.Filter.atTop
        (nhds (-(∫ x, ∑ i : Fin d, F x i * hw.weakGrad x i ∂μ))) := by
    simpa only [hseq] using hleft.neg
  have hlimit :
      -(∫ x, ∑ i : Fin d, F x i * hw.weakGrad x i ∂μ) =
        ∫ x, g x * v x ∂μ :=
    tendsto_nhds_unique hright_neg hright
  rw [weakProblemRHSOfField_eq_of_memH01 hΩ hv0 hw]
  have hscalar : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := by
    intro a b
    simpa using RCLike.inner_apply' a b
  simpa [divergenceRHSOfField, divergenceRHSIntegrandOfField, PiLp.inner_apply,
    hscalar, μ, mul_comm] using! hlimit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.weakProblemRHSOfField_eq_integral then
    throwError "Refusing to shadow existing declaration DeGiorgi.weakProblemRHSOfField_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.weakProblemRHSOfField_eq_integral ``Submission.DeGiorgi.weakProblemRHSOfField_eq_integral

end DeGiorgi
