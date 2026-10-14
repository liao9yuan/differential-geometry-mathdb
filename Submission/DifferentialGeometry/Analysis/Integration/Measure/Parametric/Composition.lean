import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
theorem aestronglyMeasurable_apply_of_ae_continuous
    {α β γ : Type*} [MeasurableSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] [TopologicalSpace.PseudoMetrizableSpace γ] {μ : _root_.MeasureTheory.Measure α}
    {F : α → β → γ} (hF : ∀ y, _root_.MeasureTheory.AEStronglyMeasurable (fun a => F a y) μ)
    (hcont : ∀ᵐ a ∂μ, Continuous (F a)) {f : α → β} (hf : _root_.MeasureTheory.AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun a => F a (f a)) μ := by
  classical
  cases isEmpty_or_nonempty α with
  | inl hα =>
    let := hα
    exact StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable
  | inr hα =>
    let : Nonempty β := ⟨f (Classical.choice hα)⟩
    have hs (s : _root_.MeasureTheory.SimpleFunc α β) : _root_.MeasureTheory.AEStronglyMeasurable (fun a => F a (s a)) μ := by
      induction s with
      | const y => exact hF y
      | @pcw s t A hA hs ht =>
        have hh := AEStronglyMeasurable.piecewise hA hs.restrict ht.restrict
        simpa only [SimpleFunc.coe_piecewise, Set.apply_piecewise] using hh
    apply aestronglyMeasurable_of_tendsto_ae (u := _root_.Filter.atTop)
      (fun n => hs (hf.stronglyMeasurable_mk.approx n))
    filter_upwards [hf.ae_eq_mk, hcont] with a ha hca
    rw [ha]
    exact (hca.tendsto _).comp (hf.stronglyMeasurable_mk.tendsto_approx a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.aestronglyMeasurable_apply_of_ae_continuous then
    throwError "Refusing to shadow existing declaration MeasureTheory.aestronglyMeasurable_apply_of_ae_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.aestronglyMeasurable_apply_of_ae_continuous ``Submission.MeasureTheory.aestronglyMeasurable_apply_of_ae_continuous

end MeasureTheory
