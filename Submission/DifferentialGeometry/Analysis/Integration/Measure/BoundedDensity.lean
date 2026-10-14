import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

namespace MeasureTheory
open _root_.MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

open _root_.MeasureTheory in
theorem isProbabilityMeasure_withDensity_ofReal {k : α → ℝ}
    (hk_nonneg : 0 ≤ᵐ[μ] k) (hk_one : ∫ x, k x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (k x))) := by
  have hk : _root_.MeasureTheory.Integrable k μ := Integrable.of_integral_ne_zero (by rw [hk_one]; exact one_ne_zero)
  constructor
  rw [_root_.MeasureTheory.withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hk hk_nonneg, hk_one, ENNReal.ofReal_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.isProbabilityMeasure_withDensity_ofReal then
    throwError "Refusing to shadow existing declaration MeasureTheory.isProbabilityMeasure_withDensity_ofReal"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.isProbabilityMeasure_withDensity_ofReal ``Submission.MeasureTheory.isProbabilityMeasure_withDensity_ofReal

open _root_.MeasureTheory in
theorem ae_withDensity_of_support_subset {k : α → ℝ} {s : Set α} {P : α → Prop}
    (hk : AEMeasurable k μ) (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hP : ∀ᵐ x ∂μ.restrict s, P x) :
    ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (k x)), P x := by
  apply (_root_.MeasureTheory.ae_withDensity_iff' hk.ennreal_ofReal).mpr
  filter_upwards [(_root_.MeasureTheory.ae_restrict_iff' hs).mp hP] with x hx hdx
  apply hx
  apply hks
  intro hkx
  exact hdx (by simp [hkx])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.ae_withDensity_of_support_subset then
    throwError "Refusing to shadow existing declaration MeasureTheory.ae_withDensity_of_support_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.ae_withDensity_of_support_subset ``Submission.MeasureTheory.ae_withDensity_of_support_subset

open _root_.MeasureTheory in
theorem withDensity_ofReal_le_const_smul_restrict {k : α → ℝ} {s : Set α}
    {C : ℝ} (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hkC : ∀ x ∈ s, k x ≤ C) :
    μ.withDensity (fun x => ENNReal.ofReal (k x)) ≤ ENNReal.ofReal C • μ.restrict s := by
  have hle : (fun x => ENNReal.ofReal (k x)) ≤ᵐ[μ]
      s.indicator (fun _ => ENNReal.ofReal C) := by
    filter_upwards [] with x
    by_cases hx : x ∈ s
    · simpa only [Set.indicator_of_mem hx] using ENNReal.ofReal_le_ofReal (hkC x hx)
    · have hkx : k x = 0 := by
        by_contra hkx
        exact hx (hks hkx)
      simp only [hkx, ENNReal.ofReal_zero, Set.indicator_of_notMem hx, le_refl]
  simpa only [_root_.MeasureTheory.withDensity_indicator hs, _root_.MeasureTheory.withDensity_const] using _root_.MeasureTheory.withDensity_mono hle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.withDensity_ofReal_le_const_smul_restrict then
    throwError "Refusing to shadow existing declaration MeasureTheory.withDensity_ofReal_le_const_smul_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.withDensity_ofReal_le_const_smul_restrict ``Submission.MeasureTheory.withDensity_ofReal_le_const_smul_restrict

variable {F : Type*} [NormedAddCommGroup F]

open _root_.MeasureTheory in
theorem integrable_withDensity_ofReal_of_support_subset {k : α → ℝ} {s : Set α}
    {f : α → F} {C : ℝ} (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hkC : ∀ x ∈ s, k x ≤ C) (hf : _root_.MeasureTheory.IntegrableOn f s μ) :
    Integrable f (μ.withDensity (fun x => ENNReal.ofReal (k x))) :=
  (hf.smul_measure ENNReal.ofReal_ne_top).mono_measure
    (withDensity_ofReal_le_const_smul_restrict hs hks hkC)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_withDensity_ofReal_of_support_subset then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_withDensity_ofReal_of_support_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_withDensity_ofReal_of_support_subset ``Submission.MeasureTheory.integrable_withDensity_ofReal_of_support_subset

open _root_.MeasureTheory in
theorem integral_withDensity_ofReal_le_const_mul_setIntegral {k h : α → ℝ} {s : Set α}
    {C : ℝ} (hk : Measurable k) (hk_nonneg : ∀ x, 0 ≤ k x)
    (hs : MeasurableSet s) (hks : Function.support k ⊆ s)
    (hkC : ∀ x ∈ s, k x ≤ C) (hh : _root_.MeasureTheory.IntegrableOn h s μ)
    (hh_nonneg : 0 ≤ᵐ[μ.restrict s] h) :
    (∫ x, h x ∂μ.withDensity (fun x => ENNReal.ofReal (k x))) ≤
      C * ∫ x in s, h x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul hk.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hk_nonneg _), smul_eq_mul]
  have hzero : ∀ x, x ∉ s → k x * h x = 0 := by
    intro x hx
    have hkx : k x = 0 := by
      by_contra hkx
      exact hx (hks hkx)
    rw [hkx, _root_.MulZeroClass.zero_mul]
  rw [← _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    ← _root_.MeasureTheory.integral_const_mul]
  have hkh : _root_.MeasureTheory.IntegrableOn (fun x => k x * h x) s μ := by
    have hint := integrable_withDensity_ofReal_of_support_subset hs hks hkC hh
    have hprod := (_root_.MeasureTheory.integrable_withDensity_iff_integrable_smul' hk.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hint
    simp only [ENNReal.toReal_ofReal (hk_nonneg _), smul_eq_mul] at hprod
    exact hprod.integrableOn
  apply _root_.MeasureTheory.integral_mono_ae hkh (hh.const_mul C)
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hs, hh_nonneg] with x hx hhx
  exact mul_le_mul_of_nonneg_right (hkC x hx) hhx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_withDensity_ofReal_le_const_mul_setIntegral then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_withDensity_ofReal_le_const_mul_setIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_withDensity_ofReal_le_const_mul_setIntegral ``Submission.MeasureTheory.integral_withDensity_ofReal_le_const_mul_setIntegral

end MeasureTheory

end
