import Submission.DifferentialGeometry.Analysis.Calculus.AbsolutelyContinuous
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.DifferentialComparison
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.UniformConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem memLp_Icc_of_lipschitz {f : ℝ → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : _root_.MeasureTheory.MemLp f 2 (volume.restrict (_root_.Set.Icc (0 : ℝ) 1)) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  obtain ⟨R, hR⟩ := (isCompact_Icc.image hf.continuous).isBounded.exists_norm_le
  apply MemLp.of_bound hf.continuous.aestronglyMeasurable R
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
  exact hR (f x) (_root_.Set.mem_image_of_mem f hx)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.memLp_Icc_of_lipschitz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.memLp_Icc_of_lipschitz target :: scope.openDecls } }

private theorem memLp_deriv_Icc_of_lipschitz {f : ℝ → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) : _root_.MeasureTheory.MemLp (deriv f) 2 (volume.restrict (_root_.Set.Icc (0 : ℝ) 1)) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict (_root_.Set.Icc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact MemLp.of_bound (aestronglyMeasurable_deriv f _) K
    (Eventually.of_forall fun x => norm_deriv_le_of_lipschitz hf)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.memLp_deriv_Icc_of_lipschitz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.memLp_deriv_Icc_of_lipschitz target :: scope.openDecls } }

private theorem norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz_real
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {x : ℝ} (hx : x ∈ _root_.Set.Icc (0 : ℝ) 1) :
    ‖f x‖ ^ 2 ≤ (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖f t‖ ^ 2) +
      2 * Real.sqrt (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) := by
  let μ : _root_.MeasureTheory.Measure ℝ := volume.restrict (_root_.Set.Icc (0 : ℝ) 1)
  let q (t : ℝ) := ‖f t‖ ^ 2
  let p (t : ℝ) := ‖f t‖ * ‖deriv f t‖
  have hfm : _root_.MeasureTheory.MemLp f 2 μ := memLp_Icc_of_lipschitz hf
  have hdfm : _root_.MeasureTheory.MemLp (deriv f) 2 μ := memLp_deriv_Icc_of_lipschitz hf
  have hp : _root_.MeasureTheory.Integrable p μ := hfm.norm.integrable_mul hdfm.norm
  have hqm : _root_.MeasureTheory.Integrable q μ :=
    (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hfm.aestronglyMeasurable).mp hfm
  have hqd : deriv q =ᵐ[_root_.MeasureTheory.MeasureSpace.volume] fun t => 2 * _root_.Inner.inner ℝ (f t) (deriv f t) := by
    filter_upwards [hf.ae_differentiableAt_real] with t ht
    exact ht.hasDerivAt.norm_sq.deriv
  have hholder : (∫ t, p t ∂μ) ≤
      Real.sqrt (∫ t, q t ∂μ) * Real.sqrt (∫ t, ‖deriv f t‖ ^ 2 ∂μ) := by
    have hf' : _root_.MeasureTheory.MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hfm
    have hdf' : _root_.MeasureTheory.MemLp (deriv f) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hdfm
    have h := _root_.MeasureTheory.integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hdf'
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hpoint (y : ℝ) (hy : y ∈ _root_.Set.Icc (0 : ℝ) 1) :
      q x ≤ q y + 2 * ∫ t, p t ∂μ := by
    have hnormac : AbsolutelyContinuousOnInterval (fun t => ‖f t‖) y x :=
      (lipschitzWith_one_norm.comp hf).lipschitzOnWith.absolutelyContinuousOnInterval
    have hqac : AbsolutelyContinuousOnInterval q y x := by
      convert hnormac.mul hnormac using 1
      funext t
      simp only [q, pow_two, Pi.mul_apply]
    have heq : q x - q y = ∫ t in y..x, 2 * _root_.Inner.inner ℝ (f t) (deriv f t) := by
      rw [← hqac.integral_deriv_eq_sub]
      exact intervalIntegral.integral_congr_ae_restrict (_root_.MeasureTheory.ae_restrict_of_ae hqd)
    have hsub : _root_.Set.uIoc y x ⊆ _root_.Set.Icc (0 : ℝ) 1 :=
      uIoc_subset_uIcc.trans (_root_.Set.uIcc_subset_Icc hy hx)
    have hp' : _root_.MeasureTheory.IntegrableOn p (_root_.Set.uIoc y x) :=
      (show _root_.MeasureTheory.IntegrableOn p (_root_.Set.Icc (0 : ℝ) 1) _root_.MeasureTheory.MeasureSpace.volume from hp).mono_set hsub
    have hi : _root_.MeasureTheory.IntegrableOn (fun t => 2 * _root_.Inner.inner ℝ (f t) (deriv f t)) (_root_.Set.uIoc y x) := by
      apply (hp'.const_mul 2).mono'
        (((hfm.aestronglyMeasurable.inner hdfm.aestronglyMeasurable).const_mul 2).mono_measure
          (Measure.restrict_mono hsub le_rfl))
      exact Eventually.of_forall fun t => by
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
    have hnorm : |q x - q y| ≤ 2 * ∫ t, p t ∂μ := by
      rw [heq, ← Real.norm_eq_abs]
      calc
        _ ≤ ∫ t in _root_.Set.uIoc y x, ‖2 * _root_.Inner.inner ℝ (f t) (deriv f t)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ t in _root_.Set.uIoc y x, 2 * p t := by
          apply _root_.MeasureTheory.integral_mono_ae hi.norm (hp'.const_mul 2)
          exact Eventually.of_forall fun t => by
            change ‖2 * _root_.Inner.inner ℝ (f t) (deriv f t)‖ ≤ 2 * (‖f t‖ * ‖deriv f t‖)
            rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)
        _ = 2 * ∫ t in _root_.Set.uIoc y x, p t := _root_.MeasureTheory.integral_const_mul _ _
        _ ≤ 2 * ∫ t, p t ∂μ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact _root_.MeasureTheory.setIntegral_mono_set hp
            (Eventually.of_forall fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            hsub.eventuallyLE
    linarith [le_abs_self (q x - q y)]
  have hbound : q x ≤ (∫ t, q t ∂μ) + 2 * ∫ t, p t ∂μ := by
    have h := _root_.MeasureTheory.setIntegral_mono_on
      (_root_.MeasureTheory.integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞))
      (hqm.add (_root_.MeasureTheory.integrableOn_const (by simp : volume (Icc (0 : ℝ) 1) ≠ ∞)))
      measurableSet_Icc hpoint
    change (∫ _ in _root_.Set.Icc (0 : ℝ) 1, q x) ≤
      ∫ t in _root_.Set.Icc (0 : ℝ) 1, q t + 2 * ∫ s, p s ∂μ at h
    rw [_root_.MeasureTheory.integral_add hqm (_root_.MeasureTheory.integrableOn_const (by simp)), _root_.MeasureTheory.setIntegral_const,
      _root_.MeasureTheory.setIntegral_const] at h
    simpa only [Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.toReal_one, one_smul] using h
  exact hbound.trans (by
    change (∫ t, q t ∂μ) + 2 * ∫ t, p t ∂μ ≤ _
    nlinarith only [hholder])

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz_real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz_real target :: scope.openDecls } }

private theorem norm_deriv_norm_le_ae_of_lipschitz
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ t ∂volume, ‖deriv (fun s => ‖f s‖) t‖ ≤ ‖deriv f t‖ := by
  have hr := lipschitzWith_one_norm.comp hf
  filter_upwards [hf.ae_differentiableAt_real, hr.ae_differentiableAt_real] with t ht hrt
  have h := DifferentialGeometry.Analysis.norm_differential_comp_le
    ht.hasFDerivAt hrt.hasFDerivAt lipschitzWith_one_norm (1 : ℝ)
  simpa only [fderiv_apply_one_eq_deriv, NNReal.coe_one, one_mul, Function.comp_def] using h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_deriv_norm_le_ae_of_lipschitz
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.norm_deriv_norm_le_ae_of_lipschitz target :: scope.openDecls } }

theorem norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {x : ℝ} (hx : x ∈ _root_.Set.Icc (0 : ℝ) 1) :
    ‖f x‖ ^ 2 ≤ (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖f t‖ ^ 2) +
      2 * Real.sqrt (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖f t‖ ^ 2) *
        Real.sqrt (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) := by
  have hr := lipschitzWith_one_norm.comp hf
  have hm := memLp_deriv_Icc_of_lipschitz hf
  have hrm := memLp_deriv_Icc_of_lipschitz hr
  have hi := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hri := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hrm.aestronglyMeasurable).mp hrm
  have he : (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (fun s => ‖f s‖) t‖ ^ 2) ≤
      ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2 := by
    apply _root_.MeasureTheory.integral_mono_ae hri hi
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae (norm_deriv_norm_le_ae_of_lipschitz hf)] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) ht 2
  have h := norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz_real hr hx
  simp only [Function.comp_def, norm_norm] at h
  apply h.trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz

theorem norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz
    {a b : ℝ → F} {K L : ℝ≥0} (ha : LipschitzWith K a) (hb : LipschitzWith L b)
    {x : ℝ} (hx : x ∈ _root_.Set.Icc (0 : ℝ) 1) :
    ‖a x - b x‖ ^ 2 ≤ (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a t - b t‖ ^ 2) +
      2 * Real.sqrt (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a t - b t‖ ^ 2) *
        Real.sqrt (2 * ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2) := by
  have ham := memLp_deriv_Icc_of_lipschitz ha
  have hbm := memLp_deriv_Icc_of_lipschitz hb
  have habm := memLp_deriv_Icc_of_lipschitz (ha.sub hb)
  have hai := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm ham.aestronglyMeasurable).mp ham
  have hbi := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm hbm.aestronglyMeasurable).mp hbm
  have habi := (_root_.MeasureTheory.memLp_two_iff_integrable_sq_norm habm.aestronglyMeasurable).mp habm
  have he : (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (fun t => a t - b t) t‖ ^ 2) ≤
      2 * ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2 := by
    rw [← _root_.MeasureTheory.integral_const_mul]
    apply _root_.MeasureTheory.integral_mono_ae habi ((hai.add hbi).const_mul 2)
    filter_upwards [_root_.MeasureTheory.ae_restrict_of_ae ha.ae_differentiableAt_real,
      _root_.MeasureTheory.ae_restrict_of_ae hb.ae_differentiableAt_real] with t hat hbt
    change ‖deriv (fun t => a t - b t) t‖ ^ 2 ≤
      2 * (‖deriv a t‖ ^ 2 + ‖deriv b t‖ ^ 2)
    rw [deriv_fun_sub hat hbt]
    have hnorm := norm_sub_le (deriv a t) (deriv b t)
    nlinarith [norm_nonneg (deriv a t - deriv b t),
      norm_nonneg (deriv a t), norm_nonneg (deriv b t),
      sq_nonneg (‖deriv a t‖ - ‖deriv b t‖)]
  apply (norm_sq_le_integral_norm_sq_add_deriv_of_lipschitz (ha.sub hb) hx).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz ``Submission.DifferentialGeometry.Analysis.Sobolev.norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz

theorem tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound
    (a b : ℕ → ℝ → F) (K L : ℕ → ℝ≥0)
    (ha : ∀ n, LipschitzWith (K n) (a n)) (hb : ∀ n, LipschitzWith (L n) (b n))
    {D : ℝ} (hD : ∀ n,
      (∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖deriv (a n) t‖ ^ 2 + ‖deriv (b n) t‖ ^ 2) ≤ D)
    (hlim : _root_.Filter.Tendsto (fun n => ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2)
      _root_.Filter.atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n t => a n t - b n t) (fun _ => 0) _root_.Filter.atTop (_root_.Set.Icc (0 : ℝ) 1) := by
  let I (n : ℕ) := ∫ t in _root_.Set.Icc (0 : ℝ) 1, ‖a n t - b n t‖ ^ 2
  let R (n : ℕ) := I n + 2 * Real.sqrt (I n) * Real.sqrt (2 * D)
  have hR : _root_.Filter.Tendsto R _root_.Filter.atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
    simpa only [R, I, Function.comp_def, Real.sqrt_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, add_zero] using
      hlim.add ((hs.const_mul 2).mul_const (Real.sqrt (2 * D)))
  have hbnd (n : ℕ) (x : ℝ) (hx : x ∈ _root_.Set.Icc (0 : ℝ) 1) :
      ‖a n x - b n x‖ ^ 2 ≤ R n := by
    apply (norm_sub_sq_le_integral_norm_sub_sq_add_deriv_of_lipschitz (ha n) (hb n) hx).trans
    dsimp only [R, I]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hD n) (by norm_num))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [((tendsto_order.1 hR).2 (ε ^ 2) (sq_pos_of_pos hε))] with n hn
  intro x hx
  have hs := (hbnd n x hx).trans_lt hn
  simpa only [dist_zero_left, norm_neg] using (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.tendstoUniformlyOn_sub_zero_of_tendsto_integral_norm_sub_sq_of_deriv_bound

end DifferentialGeometry.Analysis.Sobolev
