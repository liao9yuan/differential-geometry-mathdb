import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.IntegrableOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory
open scoped _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {X F : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem ContinuousOn.memLp_restrict_compact {S : Set X} (hS : IsCompact S)
    {f : X → F} (hf : ContinuousOn f S) (p : ℝ≥0∞) : _root_.MeasureTheory.MemLp f p (μ.restrict S) := by
  let : _root_.MeasureTheory.IsFiniteMeasure (μ.restrict S) := _root_.MeasureTheory.isFiniteMeasure_restrict.mpr hS.measure_ne_top
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hf
  apply MemLp.of_bound (hf.aestronglyMeasurable_of_isCompact hS hS.measurableSet) C
  filter_upwards [_root_.MeasureTheory.ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.MeasureTheory.ContinuousOn
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.ContinuousOn.memLp_restrict_compact then
    throwError "Refusing to shadow existing declaration MeasureTheory.ContinuousOn.memLp_restrict_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.ContinuousOn.memLp_restrict_compact ``Submission.MeasureTheory.ContinuousOn.memLp_restrict_compact

end MeasureTheory

end
