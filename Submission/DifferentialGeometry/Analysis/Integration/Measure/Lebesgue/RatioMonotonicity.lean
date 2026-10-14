import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Order.Interval.Set.Disjoint

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem setLIntegral_mul_setLIntegral_le_of_forall_mul_le
    {α : Type*} [MeasurableSpace α] {μ : _root_.MeasureTheory.Measure α}
    {f g : α → ℝ≥0∞} {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s ⊆ t)
    (hf : AEMeasurable f (μ.restrict t))
    (hg : AEMeasurable g (μ.restrict t))
    (hcross : ∀ a ∈ s, ∀ b ∈ t \ s, f b * g a ≤ f a * g b) :
    (∫⁻ x in t, f x ∂μ) * (∫⁻ x in s, g x ∂μ) ≤
      (∫⁻ x in s, f x ∂μ) * ∫⁻ x in t, g x ∂μ := by
  have hdiff : MeasurableSet (t \ s) := ht.diff hs
  have hdisj : Disjoint s (t \ s) := _root_.Set.disjoint_sdiff_right
  have hunion : s ∪ (t \ s) = t := _root_.Set.union_sdiff_cancel hst
  have hfA := hf.mono_measure (Measure.restrict_mono hst le_rfl)
  have hfB := hf.mono_measure (Measure.restrict_mono (show t \ s ⊆ t from _root_.Set.sdiff_subset) le_rfl)
  have hgA := hg.mono_measure (Measure.restrict_mono hst le_rfl)
  have hgB := hg.mono_measure (Measure.restrict_mono (show t \ s ⊆ t from _root_.Set.sdiff_subset) le_rfl)
  have hf_split : ∫⁻ x in t, f x ∂μ =
      (∫⁻ x in s, f x ∂μ) + ∫⁻ x in t \ s, f x ∂μ := by
    conv_lhs => rw [← hunion]
    exact _root_.MeasureTheory.lintegral_union hdiff hdisj
  have hg_split : ∫⁻ x in t, g x ∂μ =
      (∫⁻ x in s, g x ∂μ) + ∫⁻ x in t \ s, g x ∂μ := by
    conv_lhs => rw [← hunion]
    exact _root_.MeasureTheory.lintegral_union hdiff hdisj
  have hstar : (∫⁻ x in t \ s, f x ∂μ) * (∫⁻ x in s, g x ∂μ) ≤
      (∫⁻ x in s, f x ∂μ) * ∫⁻ x in t \ s, g x ∂μ := by
    have hleft : (∫⁻ x in t \ s, f x ∂μ) * (∫⁻ x in s, g x ∂μ) =
        ∫⁻ b in t \ s, ∫⁻ a in s, f b * g a ∂μ ∂μ := by
      rw [← _root_.MeasureTheory.lintegral_mul_const'' _ hfB]
      exact _root_.MeasureTheory.lintegral_congr fun b => (_root_.MeasureTheory.lintegral_const_mul'' _ hgA).symm
    have hright : (∫⁻ x in s, f x ∂μ) * (∫⁻ x in t \ s, g x ∂μ) =
        ∫⁻ b in t \ s, ∫⁻ a in s, f a * g b ∂μ ∂μ := by
      rw [← _root_.MeasureTheory.lintegral_const_mul'' _ hgB]
      exact _root_.MeasureTheory.lintegral_congr fun b => (_root_.MeasureTheory.lintegral_mul_const'' _ hfA).symm
    rw [hleft, hright]
    refine _root_.MeasureTheory.lintegral_mono_ae ((_root_.MeasureTheory.ae_restrict_mem hdiff).mono fun b hb => ?_)
    exact _root_.MeasureTheory.lintegral_mono_ae ((_root_.MeasureTheory.ae_restrict_mem hs).mono fun a ha => hcross a ha b hb)
  rw [hf_split, hg_split, add_mul, mul_add]
  exact add_le_add le_rfl hstar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setLIntegral_mul_setLIntegral_le_of_forall_mul_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.setLIntegral_mul_setLIntegral_le_of_forall_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setLIntegral_mul_setLIntegral_le_of_forall_mul_le ``Submission.MeasureTheory.setLIntegral_mul_setLIntegral_le_of_forall_mul_le

open _root_.MeasureTheory in
theorem setLIntegral_Iic_mul_setLIntegral_Iic_le
    {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [ClosedIicTopology α]
    {μ : _root_.MeasureTheory.Measure α} {f g : α → ℝ≥0∞} {s R : α}
    (hf : AEMeasurable f (μ.restrict (_root_.Set.Iic R)))
    (hg : AEMeasurable g (μ.restrict (_root_.Set.Iic R)))
    (hcross : ∀ ⦃a b : α⦄, a ≤ b → b ≤ R → f b * g a ≤ f a * g b)
    (hsR : s ≤ R) :
    (∫⁻ x in _root_.Set.Iic R, f x ∂μ) * (∫⁻ x in _root_.Set.Iic s, g x ∂μ) ≤
      (∫⁻ x in _root_.Set.Iic s, f x ∂μ) * ∫⁻ x in _root_.Set.Iic R, g x ∂μ := by
  apply setLIntegral_mul_setLIntegral_le_of_forall_mul_le measurableSet_Iic
    measurableSet_Iic (Iic_subset_Iic.mpr hsR) hf hg
  intro a ha b hb
  exact hcross (ha.trans (lt_of_not_ge hb.2).le) hb.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setLIntegral_Iic_mul_setLIntegral_Iic_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.setLIntegral_Iic_mul_setLIntegral_Iic_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setLIntegral_Iic_mul_setLIntegral_Iic_le ``Submission.MeasureTheory.setLIntegral_Iic_mul_setLIntegral_Iic_le

open _root_.MeasureTheory in
theorem setLIntegral_Ioc_mul_setLIntegral_Ioc_le
    {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [ClosedIicTopology α]
    {μ : _root_.MeasureTheory.Measure α} {f g : α → ℝ≥0∞} {l s R : α}
    (hf : AEMeasurable f (μ.restrict (_root_.Set.Ioc l R)))
    (hg : AEMeasurable g (μ.restrict (_root_.Set.Ioc l R)))
    (hcross : ∀ ⦃a b : α⦄, l < a → a ≤ b → b ≤ R → f b * g a ≤ f a * g b)
    (hsR : s ≤ R) :
    (∫⁻ x in _root_.Set.Ioc l R, f x ∂μ) * (∫⁻ x in _root_.Set.Ioc l s, g x ∂μ) ≤
      (∫⁻ x in _root_.Set.Ioc l s, f x ∂μ) * ∫⁻ x in _root_.Set.Ioc l R, g x ∂μ := by
  apply setLIntegral_mul_setLIntegral_le_of_forall_mul_le measurableSet_Ioc
    measurableSet_Ioc (_root_.Set.Ioc_subset_Ioc le_rfl hsR) hf hg
  intro a ha b hb
  have hsb : s < b := lt_of_not_ge (fun hbs => hb.2 ⟨hb.1.1, hbs⟩)
  exact hcross ha.1 (ha.2.trans hsb.le) hb.1.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.setLIntegral_Ioc_mul_setLIntegral_Ioc_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.setLIntegral_Ioc_mul_setLIntegral_Ioc_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.setLIntegral_Ioc_mul_setLIntegral_Ioc_le ``Submission.MeasureTheory.setLIntegral_Ioc_mul_setLIntegral_Ioc_le

end MeasureTheory
