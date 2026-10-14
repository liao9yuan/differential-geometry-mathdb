import Submission.DifferentialGeometry.Geometry.Measure.ChartNull
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Differentiation.Rademacher

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem riemannianVolumeMeasure_nondiff_null_on
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {U : Set M} (hU : IsOpen U)
    (hf : ∀ α : M, LocallyLipschitzOn
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' U)
      (f ∘ (extChartAt I α).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | x ∈ U ∧ ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0 := by
  change riemannianMeasure (I := I) g (chartAtlasPOU I M) _ = 0
  apply DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure
  intro α
  apply DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null
  rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
  filter_upwards [local_diff_ae (hf α)] with y hy
  rintro ⟨x, ⟨⟨hxU, hx⟩, hxs⟩, rfl⟩
  have hxt : extChartAt I α x ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by simpa only [extChartAt_source] using hxs)
  have hxext : x ∈ (extChartAt I α).source := by simpa only [extChartAt_source] using hxs
  have hpre : extChartAt I α x ∈ (extChartAt I α).symm ⁻¹' U := by
    change (extChartAt I α).symm (extChartAt I α x) ∈ U
    rwa [(extChartAt I α).left_inv hxext]
  have hn : (extChartAt I α).symm ⁻¹' U ∈ 𝓝[(extChartAt I α).target] (extChartAt I α x) :=
    (continuousOn_extChartAt_symm (I := I) α (extChartAt I α x) hxt).preimage_mem_nhdsWithin
      (hU.mem_nhds hpre)
  have hdiff := (hy ⟨hxt, hpre⟩).congr_nhds (nhdsWithin_inter_of_mem' hn)
  have hdiff' := hdiff.congr_nhds (nhdsWithin_extChartAt_target_eq_of_mem hxt)
  apply hx
  rw [mdifferentiableAt_iff_source_of_mem_source hxs,
    mdifferentiableWithinAt_iff_differentiableWithinAt]
  exact hdiff'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null_on ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null_on

theorem riemannianVolumeMeasure_nondiff_null
    (g : SmoothRiemannianMetric I M) (f : M → ℝ)
    (hf : ∀ α : M, LocallyLipschitzOn (extChartAt I α).target
      (f ∘ (extChartAt I α).symm)) :
    riemannianVolumeMeasure (I := I) (M := M) g
      {x : M | ¬ MDifferentiableAt I 𝓘(ℝ, ℝ) f x} = 0 := by
  have hn := riemannianVolumeMeasure_nondiff_null_on g f (U := _root_.Set.univ) isOpen_univ
    (by simpa only [_root_.Set.preimage_univ, _root_.Set.inter_univ] using hf)
  simpa only [_root_.Set.mem_univ, true_and] using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_nondiff_null

end DifferentialGeometry.Geometry.Measure

end
