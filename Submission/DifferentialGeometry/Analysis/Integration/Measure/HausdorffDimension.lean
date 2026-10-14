import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.Set _root_.MeasureTheory _root_.MeasureTheory.Measure
open scoped _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem addHaar_eq_zero_of_dimH_lt (μ : _root_.MeasureTheory.Measure E) [_root_.MeasureTheory.Measure.IsAddHaarMeasure μ]
    {s : Set E} (hs : dimH s < Module.finrank ℝ E) : μ s = 0 := by
  let e : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  have hdim : dimH (e '' s) < Module.finrank ℝ E := by
    rw [e.dimH_image]
    exact hs
  have hn : _root_.MeasureTheory.MeasureSpace.volume (e '' s) = 0 := by
    have hd : dimH (e '' s) < (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ≥0) := by
      simpa using hdim
    simpa only [NNReal.coe_natCast, _root_.MeasureTheory.hausdorffMeasure_pi_real] using hausdorffMeasure_of_dimH_lt hd
  have he : _root_.MeasureTheory.Measure.IsAddHaarMeasure (μ.map e) := e.isAddHaarMeasure_map μ
  have hn' := _root_.MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure (μ.map e) _root_.MeasureTheory.MeasureSpace.volume hn
  exact le_antisymm
    ((_root_.MeasureTheory.Measure.le_map_apply_image e.continuous.measurable.aemeasurable s).trans_eq hn') zero_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt ``Submission.DifferentialGeometry.MeasureTheory.addHaar_eq_zero_of_dimH_lt

end DifferentialGeometry.MeasureTheory
