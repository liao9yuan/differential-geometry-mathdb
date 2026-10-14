import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal

variable {α E : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [OpensMeasurableSpace α] [NormedAddCommGroup E]
  {f : α → E} {s t : Set α} {μ : Measure α}

open _root_.ContinuousOn in
theorem ContinuousOn.memLp_top_of_subset_isCompact
    (hf : ContinuousOn f s) (hs : IsCompact s) (ht : MeasurableSet t) (hts : t ⊆ s) :
    MemLp f ∞ (μ.restrict t) := by
  obtain ⟨C, hC⟩ := hs.bddAbove_image hf.norm
  apply _root_.MeasureTheory.memLp_top_of_bound (hf.aestronglyMeasurable_of_subset_isCompact hs ht hts) C
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem ht] with x hx
  exact hC (_root_.Set.mem_image_of_mem (fun y => ‖f y‖) (hts hx))

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.memLp_top_of_subset_isCompact then
    throwError "Refusing to shadow existing declaration ContinuousOn.memLp_top_of_subset_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.memLp_top_of_subset_isCompact ``Submission.ContinuousOn.memLp_top_of_subset_isCompact

open _root_.ContinuousOn in
theorem ContinuousOn.memLp_top_of_isCompact
    (hf : ContinuousOn f s) (hs : IsCompact s) (hsm : MeasurableSet s) :
    MemLp f ∞ (μ.restrict s) :=
  hf.memLp_top_of_subset_isCompact hs hsm Subset.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousOn.memLp_top_of_isCompact then
    throwError "Refusing to shadow existing declaration ContinuousOn.memLp_top_of_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousOn.memLp_top_of_isCompact ``Submission.ContinuousOn.memLp_top_of_isCompact
