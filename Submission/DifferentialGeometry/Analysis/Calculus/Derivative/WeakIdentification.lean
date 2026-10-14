import Submission.DifferentialGeometry.Analysis.Integration.Integral.LipschitzIntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace LocallyLipschitzOn
open _root_.LocallyLipschitzOn

open _root_.Filter _root_.MeasureTheory _root_.Set
open scoped _root_.Topology _root_.ContDiff

section LocalIntegrability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [SecondCountableTopology F] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  {Ω : Set E} {f : E → F}

open _root_.LocallyLipschitzOn in
theorem locallyIntegrableOn_fderiv (hf : LocallyLipschitzOn Ω f) (hΩ : IsOpen Ω) :
    LocallyIntegrableOn (fderiv ℝ f) Ω μ := by
  apply (_root_.MeasureTheory.locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  obtain ⟨L, hL, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨C, hLip⟩ := (hf.mono hLΩ).exists_lipschitzOnWith_of_compact hL
  apply (_root_.MeasureTheory.integrableOn_const (C := (C : ℝ)) hK.measure_ne_top).mono'
    (measurable_fderiv ℝ f).aestronglyMeasurable
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hK.measurableSet] with x hx
  exact norm_fderiv_le_of_lipschitzOn ℝ
    (mem_interior_iff_mem_nhds.mp (hKL hx)) hLip

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.locallyIntegrableOn_fderiv then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.locallyIntegrableOn_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.locallyIntegrableOn_fderiv ``Submission.LocallyLipschitzOn.locallyIntegrableOn_fderiv

end LocalIntegrability

section Identification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]
  {Ω : Set E} {f g : E → ℝ}

open _root_.LocallyLipschitzOn in
theorem ae_fderiv_apply_eq_neg_of_integral_mul_fderiv_eq
    (hf : LocallyLipschitzOn Ω f) (hΩ : IsOpen Ω)
    (hg : _root_.MeasureTheory.LocallyIntegrableOn g Ω μ) (v : E)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x, f x * fderiv ℝ ψ x v ∂μ) = ∫ x, g x * ψ x ∂μ) :
    ∀ᵐ x ∂μ, x ∈ Ω → fderiv ℝ f x v = -g x := by
  have hd : _root_.MeasureTheory.LocallyIntegrableOn (fun x => fderiv ℝ f x v) Ω μ :=
    (ContinuousLinearMap.apply ℝ ℝ v).locallyIntegrableOn_comp
      (hf.locallyIntegrableOn_fderiv hΩ)
  have hzero : ∀ᵐ x ∂μ, x ∈ Ω → fderiv ℝ f x v + g x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hd.add hg)
    intro ψ hψ hψc hψΩ
    have htest {u : E → ℝ} (hu : _root_.MeasureTheory.LocallyIntegrableOn u Ω μ) :
        Integrable (fun x => ψ x * u x) μ := by
      have hint : _root_.MeasureTheory.IntegrableOn (fun x => ψ x * u x) (tsupport ψ) μ :=
        IntegrableOn.continuousOn_mul hψ.continuous.continuousOn
          (hu.integrableOn_compact_subset hψΩ hψc) hψc
      apply hint.integrable_of_forall_notMem_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx, _root_.MulZeroClass.zero_mul]
    have hibp := hf.integral_fderiv_mul_eq_neg_mul_fderiv (μ := μ) hΩ
      (hψ.of_le (by simp)) hψc hψΩ v
    rw [hweak ψ hψ hψc hψΩ] at hibp
    have hid : (∫ x, ψ x * fderiv ℝ f x v ∂μ) = -(∫ x, ψ x * g x ∂μ) := by
      simpa only [mul_comm] using hibp
    simp only [Pi.add_apply, smul_eq_mul, mul_add]
    rw [_root_.MeasureTheory.integral_add (htest hd) (htest hg), hid, neg_add_cancel]
  filter_upwards [hzero] with x hx hxΩ
  exact eq_neg_of_add_eq_zero_left (hx hxΩ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LocallyLipschitzOn.ae_fderiv_apply_eq_neg_of_integral_mul_fderiv_eq then
    throwError "Refusing to shadow existing declaration LocallyLipschitzOn.ae_fderiv_apply_eq_neg_of_integral_mul_fderiv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LocallyLipschitzOn.ae_fderiv_apply_eq_neg_of_integral_mul_fderiv_eq ``Submission.LocallyLipschitzOn.ae_fderiv_apply_eq_neg_of_integral_mul_fderiv_eq

end Identification

end LocallyLipschitzOn
