import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis

open _root_.MeasureTheory
open scoped _root_.NNReal _root_.ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}

def lowerBoundedIntegral (f g : α → ℝ) (μ : _root_.MeasureTheory.Measure α) : WithTop ℝ :=
  if (∫⁻ x, ENNReal.ofReal (f x - g x) ∂μ) = ∞ then ⊤ else
    ↑((∫⁻ x, ENNReal.ofReal (f x - g x) ∂μ).toReal + ∫ x, g x ∂μ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral

theorem lowerBoundedIntegral_eq_integral (hf : _root_.MeasureTheory.Integrable f μ) (hg : _root_.MeasureTheory.Integrable g μ)
    (hgf : g ≤ᵐ[μ] f) : lowerBoundedIntegral f g μ = (↑(∫ x, f x ∂μ) : WithTop ℝ) := by
  have hnonneg : 0 ≤ᵐ[μ] (fun x ↦ f x - g x) := hgf.mono fun x hx ↦ sub_nonneg.mpr hx
  have hi : 0 ≤ ∫ x, f x - g x ∂μ := _root_.MeasureTheory.integral_nonneg_of_ae hnonneg
  have hsub : _root_.MeasureTheory.Integrable (fun x ↦ f x - g x) μ := hf.sub hg
  unfold lowerBoundedIntegral
  rw [← _root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsub hnonneg]
  simp only [ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal hi]
  rw [_root_.MeasureTheory.integral_sub hf hg, sub_add_cancel]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_integral ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_integral

theorem lowerBoundedIntegral_eq_top_iff (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ)
    (hg : _root_.MeasureTheory.Integrable g μ) (hgf : g ≤ᵐ[μ] f) :
    lowerBoundedIntegral f g μ = ⊤ ↔ ¬ _root_.MeasureTheory.Integrable f μ := by
  have hnonneg : 0 ≤ᵐ[μ] (fun x ↦ f x - g x) := hgf.mono fun x hx ↦ sub_nonneg.mpr hx
  have hi : _root_.MeasureTheory.Integrable (fun x ↦ f x - g x) μ ↔ _root_.MeasureTheory.Integrable f μ := by
    constructor
    · intro h
      have hh : _root_.MeasureTheory.Integrable (fun x ↦ (f x - g x) + g x) μ := h.add hg
      simpa only [sub_add_cancel] using hh
    · exact fun h ↦ h.sub hg
  have hm : _root_.MeasureTheory.AEStronglyMeasurable (fun x ↦ f x - g x) μ :=
    hf.sub hg.aestronglyMeasurable
  have heq := not_congr ((_root_.MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hm hnonneg).trans hi)
  simpa [lowerBoundedIntegral] using heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_top_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_top_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_top_iff ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_eq_top_iff

theorem lowerBoundedIntegral_congr_lower_bound (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ)
    (hg : _root_.MeasureTheory.Integrable g μ) (hh : _root_.MeasureTheory.Integrable h μ) (hgf : g ≤ᵐ[μ] f) (hhf : h ≤ᵐ[μ] f) :
    lowerBoundedIntegral f g μ = lowerBoundedIntegral f h μ := by
  by_cases hi : _root_.MeasureTheory.Integrable f μ
  · rw [lowerBoundedIntegral_eq_integral hi hg hgf,
      lowerBoundedIntegral_eq_integral hi hh hhf]
  · rw [(lowerBoundedIntegral_eq_top_iff hf hg hgf).2 hi,
      (lowerBoundedIntegral_eq_top_iff hf hh hhf).2 hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_lower_bound ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_lower_bound

end DifferentialGeometry.Analysis

end

noncomputable section

namespace DifferentialGeometry.Analysis

open _root_.MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f g : α → ℝ}

theorem lowerBoundedIntegral_add_measure
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f (μ + ν)) (hg : _root_.MeasureTheory.Integrable g (μ + ν))
    (hgf : g ≤ᵐ[μ + ν] f) :
    lowerBoundedIntegral f g (μ + ν) =
      lowerBoundedIntegral f g μ + lowerBoundedIntegral f g ν := by
  obtain ⟨hfμ, hfν⟩ := aestronglyMeasurable_add_measure_iff.mp hf
  obtain ⟨hgμ, hgν⟩ := integrable_add_measure.mp hg
  obtain ⟨hleμ, hleν⟩ := ae_add_measure_iff.mp hgf
  by_cases hiμ : _root_.MeasureTheory.Integrable f μ
  · by_cases hiν : _root_.MeasureTheory.Integrable f ν
    · rw [lowerBoundedIntegral_eq_integral (hiμ.add_measure hiν) hg hgf,
        lowerBoundedIntegral_eq_integral hiμ hgμ hleμ,
        lowerBoundedIntegral_eq_integral hiν hgν hleν,
        _root_.MeasureTheory.integral_add_measure hiμ hiν, WithTop.coe_add]
    · rw [(lowerBoundedIntegral_eq_top_iff hfν hgν hleν).2 hiν,
        WithTop.add_top, lowerBoundedIntegral_eq_top_iff hf hg hgf]
      exact fun h ↦ hiν h.right_of_add_measure
  · rw [(lowerBoundedIntegral_eq_top_iff hfμ hgμ hleμ).2 hiμ,
      WithTop.top_add, lowerBoundedIntegral_eq_top_iff hf hg hgf]
    exact fun h ↦ hiμ h.left_of_add_measure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_add_measure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_add_measure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_add_measure ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_add_measure

theorem lowerBoundedIntegral_Ioo_add {μ : _root_.MeasureTheory.Measure ℝ} [_root_.MeasureTheory.NullSingletonClass μ]
    {f g : ℝ → ℝ} {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f (μ.restrict (Set.Ioo a b)))
    (hg : _root_.MeasureTheory.Integrable g (μ.restrict (Set.Ioo a b)))
    (hgf : g ≤ᵐ[μ.restrict (Set.Ioo a b)] f) :
    lowerBoundedIntegral f g (μ.restrict (Set.Ioo a b)) =
      lowerBoundedIntegral f g (μ.restrict (Set.Ioo a c)) +
        lowerBoundedIntegral f g (μ.restrict (Set.Ioo c b)) := by
  have hμ : μ.restrict (Set.Ioo a b) =
      μ.restrict (Set.Ioo a c) + μ.restrict (Set.Ioo c b) := by
    simp only [_root_.MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    rw [← Set.Ioc_union_Ioc_eq_Ioc hac hcb,
      Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  rw [hμ] at hf hg hgf ⊢
  exact lowerBoundedIntegral_add_measure hf hg hgf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_Ioo_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_Ioo_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_Ioo_add ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_Ioo_add

end DifferentialGeometry.Analysis

end

noncomputable section

namespace DifferentialGeometry.Analysis

open _root_.MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℝ}

theorem integral_lower_bound_le_lowerBoundedIntegral (f g : α → ℝ) (μ : _root_.MeasureTheory.Measure α) :
    (↑(∫ x, g x ∂μ) : WithTop ℝ) ≤ lowerBoundedIntegral f g μ := by
  unfold lowerBoundedIntegral
  split
  · exact le_top
  · rw [WithTop.coe_le_coe]
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_lower_bound_le_lowerBoundedIntegral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_lower_bound_le_lowerBoundedIntegral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_lower_bound_le_lowerBoundedIntegral ``Submission.DifferentialGeometry.Analysis.integral_lower_bound_le_lowerBoundedIntegral

theorem lowerBoundedIntegral_mono
    (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) (hh : _root_.MeasureTheory.AEStronglyMeasurable h μ)
    (hg : _root_.MeasureTheory.Integrable g μ) (hgf : g ≤ᵐ[μ] f) (hfh : f ≤ᵐ[μ] h) :
    lowerBoundedIntegral f g μ ≤ lowerBoundedIntegral h g μ := by
  by_cases hi : _root_.MeasureTheory.Integrable h μ
  · have hfi : _root_.MeasureTheory.Integrable f μ := _root_.MeasureTheory.integrable_of_le_of_le hf hgf hfh hg hi
    rw [lowerBoundedIntegral_eq_integral hfi hg hgf,
      lowerBoundedIntegral_eq_integral hi hg (hgf.trans hfh), WithTop.coe_le_coe]
    exact _root_.MeasureTheory.integral_mono_ae hfi hi hfh
  · rw [(lowerBoundedIntegral_eq_top_iff hh hg (hgf.trans hfh)).2 hi]
    exact le_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_mono ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_mono

theorem lowerBoundedIntegral_congr_ae (hfg : f =ᵐ[μ] h) (g : α → ℝ) :
    lowerBoundedIntegral f g μ = lowerBoundedIntegral h g μ := by
  unfold lowerBoundedIntegral
  have heq : (∫⁻ x, ENNReal.ofReal (f x - g x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (h x - g x) ∂μ :=
    _root_.MeasureTheory.lintegral_congr_ae (hfg.mono fun x hx => by dsimp only; rw [hx])
  rw [heq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_ae then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_ae"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_ae ``Submission.DifferentialGeometry.Analysis.lowerBoundedIntegral_congr_ae

end DifferentialGeometry.Analysis
