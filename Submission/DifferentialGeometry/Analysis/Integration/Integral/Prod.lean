import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Module.Dual

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace MeasureTheory
open _root_.MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite ν]

open _root_.MeasureTheory in
private theorem integral_prod_nonneg {f : α × β → ℝ}
    (hf : _root_.MeasureTheory.Integrable f (μ.prod ν)) (hpos : 0 ≤ᵐ[μ.prod ν] f) :
    ∫ p, f p ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  have hslice := (_root_.MeasureTheory.integrable_prod_iff hf.aestronglyMeasurable).mp hf
  have hpos_slice := Measure.ae_ae_of_ae_prod hpos
  have houter_pos : 0 ≤ᵐ[μ] fun x => ∫ y, f (x, y) ∂ν := by
    filter_upwards [hpos_slice] with x hx
    exact _root_.MeasureTheory.integral_nonneg_of_ae hx
  rw [_root_.MeasureTheory.integral_eq_lintegral_of_nonneg_ae hpos hf.aestronglyMeasurable,
    _root_.MeasureTheory.integral_eq_lintegral_of_nonneg_ae houter_pos hf.integral_prod_left.aestronglyMeasurable,
    _root_.MeasureTheory.lintegral_prod _ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  congr 1
  apply _root_.MeasureTheory.lintegral_congr_ae
  filter_upwards [hslice.1, hpos_slice] with x hx hxp
  exact (_root_.MeasureTheory.ofReal_integral_eq_lintegral_ofReal hx hxp).symm

run_cmd do
  let target := ``Submission.MeasureTheory.integral_prod_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_prod_nonneg target :: scope.openDecls } }

open _root_.MeasureTheory in
private theorem integral_prod_real {f : α × β → ℝ} (hf : _root_.MeasureTheory.Integrable f (μ.prod ν)) :
    ∫ p, f p ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  have hp := hf.pos_part
  have hn := hf.neg_part
  have hps := (_root_.MeasureTheory.integrable_prod_iff hp.aestronglyMeasurable).mp hp
  have hns := (_root_.MeasureTheory.integrable_prod_iff hn.aestronglyMeasurable).mp hn
  calc
    ∫ p, f p ∂μ.prod ν =
        (∫ p, _root_.Max.max (f p) 0 ∂μ.prod ν) - ∫ p, _root_.Max.max (-f p) 0 ∂μ.prod ν := by
      rw [← _root_.MeasureTheory.integral_sub hp hn]
      simp only [max_zero_sub_max_neg_zero_eq_self]
    _ = (∫ x, ∫ y, _root_.Max.max (f (x, y)) 0 ∂ν ∂μ) -
        ∫ x, ∫ y, _root_.Max.max (-f (x, y)) 0 ∂ν ∂μ := by
      rw [integral_prod_nonneg hp (Filter.Eventually.of_forall fun _ => le_max_right _ _),
        integral_prod_nonneg hn (Filter.Eventually.of_forall fun _ => le_max_right _ _)]
    _ = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
      rw [← _root_.MeasureTheory.integral_sub hp.integral_prod_left hn.integral_prod_left]
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [hps.1, hns.1] with x hxp hxn
      rw [← _root_.MeasureTheory.integral_sub hxp hxn]
      simp only [max_zero_sub_max_neg_zero_eq_self]

run_cmd do
  let target := ``Submission.MeasureTheory.integral_prod_real
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.integral_prod_real target :: scope.openDecls } }

open _root_.MeasureTheory _root_.MeasureTheory.Integrable in
theorem Integrable.integral_prod {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : α × β → F} (hf : _root_.MeasureTheory.Integrable f (μ.prod ν)) :
    ∫ p, f p ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ := by
  by_cases hF : CompleteSpace F
  · let _ := hF
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
    intro L
    rw [← L.integral_comp_comm hf, ← L.integral_comp_comm hf.integral_prod_left,
      integral_prod_real (L.integrable_comp hf)]
    apply _root_.MeasureTheory.integral_congr_ae
    filter_upwards [(_root_.MeasureTheory.integrable_prod_iff hf.aestronglyMeasurable).mp hf |>.1] with x hx
    exact L.integral_comp_comm hx
  · simp only [_root_.MeasureTheory.integral_of_not_completeSpace hF]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.Integrable
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.Integrable.integral_prod then
    throwError "Refusing to shadow existing declaration MeasureTheory.Integrable.integral_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.Integrable.integral_prod ``Submission.MeasureTheory.Integrable.integral_prod

open _root_.Set in
open _root_.MeasureTheory in
theorem integral_eq_integral_restrict_prod_of_support
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [_root_.MeasureTheory.SFinite μ] {s : Set α} {t : Set β}
    {f : α × β → E}
    (hfs : ∀ p, p ∉ s ×ˢ t → f p = 0) :
    (∫ p, f p ∂μ.prod ν) = ∫ p, f p ∂(μ.restrict s).prod (ν.restrict t) := by
  rw [Measure.prod_restrict]
  symm
  apply _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  exact hfs p hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_eq_integral_restrict_prod_of_support then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_eq_integral_restrict_prod_of_support"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_eq_integral_restrict_prod_of_support ``Submission.MeasureTheory.integral_eq_integral_restrict_prod_of_support

open _root_.Set in
open _root_.MeasureTheory in
theorem integral_eq_integral_restrict_prod_of_support_subset
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [_root_.MeasureTheory.SFinite μ]
    {s : Set α} {t t₀ : Set β} (ht : MeasurableSet t₀) (hsub : t₀ ⊆ t)
    {f : α × β → E}
    (hfs : ∀ p, p ∉ s ×ˢ t₀ → f p = 0) :
    (∫ p, f p ∂μ.prod (ν.restrict t)) =
      ∫ p, f p ∂(μ.restrict s).prod (ν.restrict t₀) := by
  have h := integral_eq_integral_restrict_prod_of_support
    (μ := μ) (ν := ν.restrict t) hfs
  rwa [Measure.restrict_restrict ht, inter_eq_left.mpr hsub] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integral_eq_integral_restrict_prod_of_support_subset then
    throwError "Refusing to shadow existing declaration MeasureTheory.integral_eq_integral_restrict_prod_of_support_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integral_eq_integral_restrict_prod_of_support_subset ``Submission.MeasureTheory.integral_eq_integral_restrict_prod_of_support_subset


end MeasureTheory
