import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

open _root_.MeasureTheory in
private theorem aestronglyMeasurable_of_continuous_injective
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] {μ : _root_.MeasureTheory.Measure α} {f : α → E} {j : E → F}
    (hj : Continuous j) (hinj : Function.Injective j)
    (hf : _root_.MeasureTheory.AEStronglyMeasurable (j ∘ f) μ) : _root_.MeasureTheory.AEStronglyMeasurable f μ := by
  borelize E F
  exact ((hj.measurableEmbedding hinj).aemeasurable_comp_iff.mp hf.aemeasurable).aestronglyMeasurable

run_cmd do
  let target := ``Submission.MeasureTheory.aestronglyMeasurable_of_continuous_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `MeasureTheory.aestronglyMeasurable_of_continuous_injective target :: scope.openDecls } }

open _root_.MeasureTheory in
theorem exists_lp_lift_of_ae_exists_norm_le
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] {μ : _root_.MeasureTheory.Measure α} {p : ℝ≥0∞}
    {j : E → F} (hj : Continuous j) (hinj : Function.Injective j)
    {g : α → F} (hg : _root_.MeasureTheory.AEStronglyMeasurable g μ)
    {b : α → ℝ} (hb : _root_.MeasureTheory.MemLp b p μ)
    (h : ∀ᵐ a ∂μ, ∃ e : E, j e = g a ∧ ‖e‖ ≤ b a) :
    ∃ v : _root_.MeasureTheory.Lp E p μ, (fun a => j (v a)) =ᵐ[μ] g ∧
      ∀ᵐ a ∂μ, ‖v a‖ ≤ b a := by
  classical
  let f : α → E := fun a =>
    if h : ∃ e : E, j e = g a ∧ ‖e‖ ≤ b a then h.choose else 0
  have hf : ∀ᵐ a ∂μ, j (f a) = g a ∧ ‖f a‖ ≤ b a := by
    filter_upwards [h] with a ha
    simpa only [f, dif_pos ha] using ha.choose_spec
  have hfg : (j ∘ f) =ᵐ[μ] g := hf.mono fun _ ha => ha.1
  have hfm : _root_.MeasureTheory.AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_continuous_injective hj hinj (hg.congr hfg.symm)
  have hLp : _root_.MeasureTheory.MemLp f p μ := hb.mono' hfm (hf.mono fun _ ha => ha.2)
  refine ⟨hLp.toLp f, ?_, ?_⟩
  · filter_upwards [hLp.coeFn_toLp, hf] with a ha hfa
    exact (congrArg j ha).trans hfa.1
  · filter_upwards [hLp.coeFn_toLp, hf] with a ha hfa
    simpa only [ha] using hfa.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.exists_lp_lift_of_ae_exists_norm_le then
    throwError "Refusing to shadow existing declaration MeasureTheory.exists_lp_lift_of_ae_exists_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.exists_lp_lift_of_ae_exists_norm_le ``Submission.MeasureTheory.exists_lp_lift_of_ae_exists_norm_le

end MeasureTheory
