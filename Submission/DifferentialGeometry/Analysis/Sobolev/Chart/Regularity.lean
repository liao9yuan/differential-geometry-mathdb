import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.MeasureComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}

private theorem contMDiffAt_of_chart_regularities
    {α x : M} (hx : x ∈ (extChartAt I α).source) {f : M → ℝ}
    (hchart : ContMDiffAt I 𝓘(ℝ, E) n (extChartAt I α) x)
    (hf : ContDiffAt ℝ n (chartPushedRaw I α f)
      (toEuclidean (E := E) (extChartAt I α x))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f x := by
  let coord : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun y => toEuclidean (E := E) (extChartAt I α y)
  have hto : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      n (toEuclidean (E := E)) (extChartAt I α x) :=
    contMDiffAt_iff_contDiffAt.mpr (toEuclidean (E := E)).contDiff.contDiffAt
  have hcoord : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      n coord x := hto.comp x hchart
  have hraw : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
      𝓘(ℝ, ℝ) n (chartPushedRaw I α f) (coord x) :=
    contMDiffAt_iff_contDiffAt.mpr hf
  refine (hraw.comp x hcoord).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_extChartAt_source α).mem_nhds hx] with y hy
  have htarget : coord y ∈ chartTargetEuclid (I := I) α :=
    ⟨extChartAt I α y, (extChartAt I α).map_source hy, rfl⟩
  rw [Function.comp_apply, chartPushedRaw_apply_of_mem α f htarget]
  simp only [coord, ContinuousLinearEquiv.symm_apply_apply, (extChartAt I α).left_inv hy]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_chart_regularities
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_chart_regularities target :: scope.openDecls } }

theorem contMDiffAt_of_contDiffAt_chartPushedRaw
    (α : M) {f : M → ℝ}
    (hf : ContDiffAt ℝ n (chartPushedRaw I α f)
      (toEuclidean (E := E) (extChartAt I α α))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f α :=
  contMDiffAt_of_chart_regularities (mem_extChartAt_source α) contMDiffAt_extChartAt hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw

theorem contMDiffAt_of_contDiffAt_chartPushedRaw_of_mem_source
    [IsManifold I n M] {α x : M} (hx : x ∈ (extChartAt I α).source) {f : M → ℝ}
    (hf : ContDiffAt ℝ n (chartPushedRaw I α f)
      (toEuclidean (E := E) (extChartAt I α x))) :
    ContMDiffAt I 𝓘(ℝ, ℝ) n f x :=
  contMDiffAt_of_chart_regularities hx
    (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)) hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw_of_mem_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw_of_mem_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw_of_mem_source ``Submission.DifferentialGeometry.Analysis.Sobolev.Chart.contMDiffAt_of_contDiffAt_chartPushedRaw_of_mem_source

end DifferentialGeometry.Analysis.Sobolev.Chart
