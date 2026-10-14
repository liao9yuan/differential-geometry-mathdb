import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Integration

noncomputable section

open _root_.MeasureTheory _root_.Real _root_.Set

variable {α : Type*} [MeasurableSpace α]

theorem withDensity_prob
    (μ : _root_.MeasureTheory.Measure α) {ρ : α -> Real}
    (hρi : _root_.MeasureTheory.Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    (hmass : (∫ x, ρ x ∂μ) = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [_root_.MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hρi hρ0, hmass]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.withDensity_prob then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.withDensity_prob"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.withDensity_prob ``Submission.DifferentialGeometry.Analysis.Integration.withDensity_prob

theorem int_log_le_moment
    {ν : _root_.MeasureTheory.Measure α} [_root_.MeasureTheory.IsProbabilityMeasure ν]
    {X : α -> Real} {p : Real} (hp : 0 < p)
    (hX : ∀ᵐ x ∂ν, 0 < X x)
    (hlog : _root_.MeasureTheory.Integrable (fun x => Real.log (X x)) ν)
    (hmom : _root_.MeasureTheory.Integrable (fun x => X x ^ p) ν) :
    (∫ x, Real.log (X x) ∂ν) ≤
      Real.log (∫ x, X x ^ p ∂ν) / p := by
  let F : α -> Real := fun x => p * Real.log (X x)
  have hF : _root_.MeasureTheory.Integrable F ν := by
    simpa only [F] using hlog.const_mul p
  have hexp_eq :
      (Real.exp ∘ F) =ᵐ[ν] (fun x => X x ^ p) := by
    filter_upwards [hX] with x hx
    simp only [Function.comp_apply, F]
    rw [Real.rpow_def_of_pos hx p, mul_comm]
  have hexp : _root_.MeasureTheory.Integrable (Real.exp ∘ F) ν :=
    hmom.congr hexp_eq.symm
  have hJ :
      Real.exp (∫ x, F x ∂ν) ≤ ∫ x, Real.exp (F x) ∂ν := by
    simpa only [Function.comp_apply] using
      (convexOn_exp.map_integral_le _root_.Real.continuousOn_exp isClosed_univ
        (by simp) hF hexp)
  have hJ' :
      Real.exp (p * ∫ x, Real.log (X x) ∂ν) ≤
        ∫ x, X x ^ p ∂ν := by
    simpa only [F, _root_.MeasureTheory.integral_const_mul] using
      hJ.trans_eq (_root_.MeasureTheory.integral_congr_ae hexp_eq)
  have hmoment_pos : 0 < ∫ x, X x ^ p ∂ν :=
    lt_of_lt_of_le (Real.exp_pos _) hJ'
  have hlog_bound :
      p * (∫ x, Real.log (X x) ∂ν) ≤
        Real.log (∫ x, X x ^ p ∂ν) := by
    exact (Real.le_log_iff_exp_le hmoment_pos).2 hJ'
  rw [le_div_iff₀ hp]
  simpa only [mul_comm] using hlog_bound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.int_log_le_moment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.int_log_le_moment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.int_log_le_moment ``Submission.DifferentialGeometry.Analysis.Integration.int_log_le_moment

theorem entropy_le_moment
    (μ : _root_.MeasureTheory.Measure α) {v : α → Real} {q : Real} (hq : 2 < q)
    (hvpos : ∀ᵐ x ∂μ, 0 < v x)
    (hv2 : _root_.MeasureTheory.Integrable (fun x => v x ^ 2) μ)
    (hmass : (∫ x, v x ^ 2 ∂μ) = 1)
    (hlog : _root_.MeasureTheory.Integrable (fun x => v x ^ 2 * Real.log (v x)) μ)
    (hmom : _root_.MeasureTheory.Integrable (fun x => v x ^ q) μ) :
    (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) ≤
      2 * (Real.log (∫ x, v x ^ q ∂μ) / (q - 2)) := by
  let ρ : α → ENNReal := fun x => ENNReal.ofReal (v x ^ 2)
  let ν : _root_.MeasureTheory.Measure α := μ.withDensity ρ
  have hρ : AEMeasurable ρ μ := by
    exact hv2.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂μ, ρ x < ⊤ := by
    filter_upwards with x
    simp only [ρ, ENNReal.ofReal_lt_top]
  have hsq0 : 0 ≤ᵐ[μ] fun x => v x ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg (v x)
  let : _root_.MeasureTheory.IsProbabilityMeasure ν := by
    dsimp only [ν, ρ]
    exact withDensity_prob μ hv2 hsq0 hmass
  have hvposν : ∀ᵐ x ∂ν, 0 < v x := by
    exact (_root_.MeasureTheory.withDensity_absolutelyContinuous μ ρ).ae_le hvpos
  have hlogν : _root_.MeasureTheory.Integrable (fun x => Real.log (v x)) ν := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
    refine hlog.congr ?_
    filter_upwards with x
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
  have hmomν : _root_.MeasureTheory.Integrable (fun x => v x ^ (q - 2)) ν := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
    refine hmom.congr ?_
    filter_upwards [hvpos] with x hx
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
    rw [← Real.rpow_natCast (v x) 2, ← Real.rpow_add hx]
    congr 1
    ring
  have hlog_eq :
      (∫ x, Real.log (v x) ∂ν) =
        ∫ x, v x ^ 2 * Real.log (v x) ∂μ := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
  have hmom_eq :
      (∫ x, v x ^ (q - 2) ∂ν) = ∫ x, v x ^ q ∂μ := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [hvpos] with x hx
    simp only [ρ, ENNReal.toReal_ofReal (sq_nonneg (v x)), smul_eq_mul]
    rw [← Real.rpow_natCast (v x) 2, ← Real.rpow_add hx]
    congr 1
    ring
  have hJ := int_log_le_moment (ν := ν) (X := v) (p := q - 2)
    (sub_pos.mpr hq) hvposν hlogν hmomν
  rw [hlog_eq, hmom_eq] at hJ
  calc
    (∫ x, v x ^ 2 * Real.log (v x ^ 2) ∂μ) =
        2 * ∫ x, v x ^ 2 * Real.log (v x) ∂μ := by
      rw [← _root_.MeasureTheory.integral_const_mul]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hvpos] with x hx
      rw [pow_two, Real.log_mul hx.ne' hx.ne']
      ring
    _ ≤ 2 * (Real.log (∫ x, v x ^ q ∂μ) / (q - 2)) :=
      mul_le_mul_of_nonneg_left hJ (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.entropy_le_moment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.entropy_le_moment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.entropy_le_moment ``Submission.DifferentialGeometry.Analysis.Integration.entropy_le_moment

theorem entropy_support_le
    (μ : _root_.MeasureTheory.Measure α) [_root_.MeasureTheory.IsFiniteMeasure μ] {w : α → Real} {U : Set α}
    (hwmeas : Measurable w) (hwi : _root_.MeasureTheory.Integrable w μ)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∫ x, w x ∂μ) = 1)
    (hent : _root_.MeasureTheory.Integrable (fun x => w x * Real.log (w x)) μ)
    (hsupp : Function.support w ⊆ U) :
    -(∫ x, w x * Real.log (w x) ∂μ) ≤ Real.log (μ U).toReal := by
  let ρ : α → ENNReal := fun x => ENNReal.ofReal (w x)
  let ν : _root_.MeasureTheory.Measure α := μ.withDensity ρ
  let X : α → Real := fun x => if w x = 0 then 1 else (w x)⁻¹
  have hρ : AEMeasurable ρ μ := hwmeas.aemeasurable.ennreal_ofReal
  have hρtop : ∀ᵐ x ∂μ, ρ x < ⊤ := by
    filter_upwards with x
    simp only [ρ, ENNReal.ofReal_lt_top]
  let : _root_.MeasureTheory.IsProbabilityMeasure ν := by
    dsimp only [ν, ρ]
    exact withDensity_prob μ hwi (Filter.Eventually.of_forall hw0) hmass
  have hXmeas : Measurable X := by
    dsimp only [X]
    exact Measurable.ite (hwmeas (_root_.MeasurableSingletonClass.measurableSet_singleton 0))
      measurable_const hwmeas.inv
  have hXpos (x : α) : 0 < X x := by
    dsimp only [X]
    split_ifs with hx
    · norm_num
    · exact inv_pos.mpr (lt_of_le_of_ne (hw0 x) (Ne.symm hx))
  have hXint : _root_.MeasureTheory.Integrable X ν := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
    refine Integrable.mono' (_root_.MeasureTheory.integrable_const (1 : Real)) ?_ ?_
    · exact hρ.ennreal_toReal.aestronglyMeasurable.mul
        hXmeas.aestronglyMeasurable
    · filter_upwards with x
      dsimp only [ρ, X]
      by_cases hx : w x = 0
      · simp only [hx, ENNReal.ofReal_zero, ENNReal.toReal_zero, if_pos,
          smul_eq_mul, _root_.MulZeroClass.zero_mul, norm_zero]
        exact zero_le_one
      · simp only [ENNReal.toReal_ofReal (hw0 x), if_neg hx, smul_eq_mul,
          mul_inv_cancel₀ hx, _root_.NormOneClass.norm_one, le_refl]
  have hlogint : _root_.MeasureTheory.Integrable (fun x => Real.log (X x)) ν := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul₀' hρ hρtop]
    refine hent.neg.congr ?_
    filter_upwards with x
    dsimp only [ρ, X]
    by_cases hx : w x = 0
    · simp [hx]
    · simp only [ENNReal.toReal_ofReal (hw0 x), if_neg hx, smul_eq_mul,
        Real.log_inv, Pi.neg_apply]
      ring
  have hlogeq :
      (∫ x, Real.log (X x) ∂ν) = -(∫ x, w x * Real.log (w x) ∂μ) := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
    rw [← _root_.MeasureTheory.integral_neg]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [ρ, X]
    by_cases hx : w x = 0
    · simp only [hx, ENNReal.ofReal_zero, ENNReal.toReal_zero, if_pos,
        smul_eq_mul, _root_.MulZeroClass.zero_mul, Real.log_one, neg_zero]
    · simp only [ENNReal.toReal_ofReal (hw0 x), if_neg hx, smul_eq_mul,
        Real.log_inv]
      ring
  let S : Set α := {x | w x ≠ 0}
  have hS : MeasurableSet S := by
    rw [show S = (w ⁻¹' {0})ᶜ by ext x; simp [S]]
    exact (hwmeas (_root_.MeasurableSingletonClass.measurableSet_singleton 0)).compl
  have hmoment : (∫ x, X x ∂ν) = (μ S).toReal := by
    rw [show ν = μ.withDensity ρ by rfl]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hρ hρtop]
    calc
      (∫ x, (ρ x).toReal • X x ∂μ) =
          ∫ x, S.indicator (fun _ => (1 : Real)) x ∂μ := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards with x
        dsimp only [ρ, X, S]
        by_cases hx : w x = 0
        · have hxS : x ∉ {y | w y ≠ 0} := fun hne => hne hx
          rw [Set.indicator_of_notMem hxS]
          simp only [hx, ENNReal.ofReal_zero, ENNReal.toReal_zero, if_pos,
            smul_eq_mul, _root_.MulZeroClass.zero_mul]
        · have hxS : x ∈ {y | w y ≠ 0} := by
            change w x ≠ 0
            exact hx
          rw [Set.indicator_of_mem hxS]
          simp only [ENNReal.toReal_ofReal (hw0 x), if_neg hx, smul_eq_mul,
            mul_inv_cancel₀ hx]
      _ = (μ S).toReal := _root_.MeasureTheory.integral_indicator_one hS
  have hJ := int_log_le_moment (ν := ν) (X := X) (p := (1 : Real))
    (by norm_num) (Filter.Eventually.of_forall hXpos) hlogint (by
      simpa only [Real.rpow_one] using hXint)
  have hmoment_pos : 0 < ∫ x, X x ∂ν := by
    rw [_root_.MeasureTheory.integral_pos_iff_support_of_nonneg (fun x => (hXpos x).le) hXint]
    have hsuppX : Function.support X = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (hXpos x).ne'
    rw [hsuppX, _root_.MeasureTheory.IsProbabilityMeasure.measure_univ]
    norm_num
  have hSU : S ⊆ U := by
    intro x hx
    exact hsupp hx
  have hreal_le : (μ S).toReal ≤ (μ U).toReal :=
    ENNReal.toReal_mono (_root_.MeasureTheory.measure_ne_top μ U) (_root_.MeasureTheory.measure_mono hSU)
  calc
    -(∫ x, w x * Real.log (w x) ∂μ) =
        ∫ x, Real.log (X x) ∂ν := hlogeq.symm
    _ ≤ Real.log (∫ x, X x ^ (1 : Real) ∂ν) / 1 := hJ
    _ = Real.log (∫ x, X x ∂ν) := by
      simp only [Real.rpow_one, div_one]
    _ ≤ Real.log (μ U).toReal := by
      apply Real.log_le_log hmoment_pos
      rw [hmoment]
      exact hreal_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Integration.entropy_support_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Integration.entropy_support_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Integration.entropy_support_le ``Submission.DifferentialGeometry.Analysis.Integration.entropy_support_le

end

end DifferentialGeometry.Analysis.Integration
