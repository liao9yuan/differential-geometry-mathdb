import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_image_eq_target
    [I.Boundaryless] (α : M) :
    (extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)
      = (extChartAt I α).target := by
  rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]
  exact (extChartAt I α).image_source_eq_target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_eq_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_eq_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_eq_target ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_eq_target

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid
    [I.Boundaryless] (α : M) :
    toEuclidean ''
        ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      = chartTargetEuclid (I := I) (M := M) α := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_target_diff_image_eq_empty
    [I.Boundaryless] (α : M) :
    ((extChartAt I α).target : Set E) \
        ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      = (∅ : Set E) := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]
  exact Set.sdiff_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_eq_empty ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_eq_empty

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
    [I.Boundaryless] (α : M) :
    chartTargetEuclid (I := I) (M := M) α \
        (toEuclidean ''
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))
      = (∅ : Set EuclN) := by
  rw [chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid (I := I) (M := M) α]
  exact Set.sdiff_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_target_diff_image_measure_zero
    [I.Boundaryless] (α : M) :
    (MeasureTheory.volume : _root_.MeasureTheory.Measure E)
        (((extChartAt I α).target : Set E) \
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))) = 0 := by
  rw [chartLeviCivitaGoodSet_target_diff_image_eq_empty (I := I) α]
  exact MeasureTheory.measure_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_measure_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_measure_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_measure_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_target_diff_image_measure_zero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero
    [I.Boundaryless] (α : M) (μ : _root_.MeasureTheory.Measure E) :
    (μ.restrict ((extChartAt I α).target : Set E))
        (((extChartAt I α).target : Set E) \
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))) = 0 := by
  rw [chartLeviCivitaGoodSet_target_diff_image_eq_empty (I := I) α]
  exact MeasureTheory.measure_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_restrict_target_diff_image_measure_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero
    [I.Boundaryless] (α : M) :
    (MeasureTheory.volume : _root_.MeasureTheory.Measure EuclN)
        (chartTargetEuclid (I := I) (M := M) α \
          (toEuclidean ''
            ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))) = 0 := by
  rw [chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
      (I := I) (M := M) α]
  exact MeasureTheory.measure_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_measure_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem chartLeviCivitaGoodSet_image_complement_measureZero
    [I.Boundaryless] (α : M) :
    ((MeasureTheory.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α \
          (toEuclidean ''
            ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)))) = 0 := by
  rw [chartLeviCivitaGoodSet_chartTargetEuclid_diff_image_eq_empty
      (I := I) (M := M) α]
  exact MeasureTheory.measure_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_complement_measureZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_complement_measureZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_complement_measureZero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLeviCivitaGoodSet_image_complement_measureZero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem mem_image_chartLeviCivitaGoodSet_iff_mem_target
    [I.Boundaryless] (α : M) (y : E) :
    y ∈ (extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α)
      ↔ y ∈ (extChartAt I α).target := by
  rw [chartLeviCivitaGoodSet_image_eq_target (I := I) α]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_image_chartLeviCivitaGoodSet_iff_mem_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_image_chartLeviCivitaGoodSet_iff_mem_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_image_chartLeviCivitaGoodSet_iff_mem_target ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_image_chartLeviCivitaGoodSet_iff_mem_target

omit [NeZero (Module.finrank ℝ E)] in
theorem mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid
    [I.Boundaryless] (α : M) (y : EuclN) :
    y ∈ toEuclidean ''
          ((extChartAt I α) '' (chartLeviCivitaGoodSet (I := I) α))
      ↔ y ∈ chartTargetEuclid (I := I) (M := M) α := by
  rw [chartLeviCivitaGoodSet_imageEuclid_eq_chartTargetEuclid (I := I) (M := M) α]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.mem_imageEuclid_chartLeviCivitaGoodSet_iff_mem_chartTargetEuclid

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
