import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

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

theorem chartLocalMeasure_null_of_chart_image_null
    (g : SmoothRiemannianMetric I M) (α : M)
    {A : Set M}
    (hA : modelHaar (E := E)
      ((extChartAt I α) '' (A ∩ (chartAt H α).source)) = 0) :
    chartLocalMeasure (I := I) g α A = 0 := by
  classical
  obtain ⟨N, hAN, hN, hNzero⟩ :=
    _root_.MeasureTheory.exists_measurable_superset_of_null hA
  have hhaar : ∀ᵐ y ∂modelHaar (E := E), y ∉ N :=
    measure_eq_zero_iff_ae_notMem.mp hNzero
  have hchart : ∀ᵐ x ∂chartLocalMeasure (I := I) g α,
      x ∈ (chartAt H α).source → extChartAt I α x ∉ N :=
    ae_chart_of_haar (I := I) g α hN.compl hhaar
  have hout : chartLocalMeasure (I := I) g α
      ((chartAt H α).source)ᶜ = 0 :=
    chartLocalMeasure_apply_of_disjoint_source (I := I) g α
      (chartAt H α).open_source.measurableSet.compl
      (show Disjoint ((chartAt H α).source)ᶜ
        (chartAt H α).source from disjoint_compl_left)
  have hsource : ∀ᵐ x ∂chartLocalMeasure (I := I) g α,
      x ∈ (chartAt H α).source := by
    simpa only [_root_.Set.mem_compl_iff, _root_.Classical.not_not] using
      measure_eq_zero_iff_ae_notMem.mp hout
  rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
  filter_upwards [hchart, hsource] with x hx hxs
  intro hxA
  exact hx hxs (hAN ⟨x, ⟨hxA, hxs⟩, rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null ``Submission.DifferentialGeometry.Geometry.Measure.chartLocalMeasure_null_of_chart_image_null

theorem riemannianMeasure_null_of_chartLocalMeasure
    [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M _root_.Set.univ)
    {A : Set M}
    (hA : ∀ α : M, chartLocalMeasure (I := I) g α A = 0) :
    riemannianMeasure (I := I) g ρ A = 0 := by
  classical
  let J : Set M := {α : M | (Function.support (ρ α)).Nonempty}
  let w : M → MeasureTheory.Measure M := fun α =>
    (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x))
  let : Countable J :=
    (countable_nonempty_support_of_pou (I := I) ρ).to_subtype
  have hoff : ∀ α : M, α ∉ J → w α = 0 := by
    intro α hα
    have hweight : (fun x : M => ENNReal.ofReal (ρ α x)) = 0 := by
      funext x
      have hρα : ρ α x = 0 := by
        by_contra hne
        exact hα ⟨x, hne⟩
      simp only [hρα, ENNReal.ofReal_zero, Pi.zero_apply]
    change (chartLocalMeasure (I := I) g α).withDensity
      (fun x : M => ENNReal.ofReal (ρ α x)) = 0
    rw [hweight, _root_.MeasureTheory.withDensity_zero]
  have hsum : riemannianMeasure (I := I) g ρ =
      MeasureTheory.Measure.sum (fun α : J => w α.val) := by
    change MeasureTheory.Measure.sum w = _
    refine MeasureTheory.Measure.ext (fun B hB => ?_)
    rw [MeasureTheory.Measure.sum_apply _ hB,
      MeasureTheory.Measure.sum_apply _ hB]
    refine tsum_subtype_eq_of_support_subset ?_
    intro α hα
    by_contra hnot
    exact hα (by
      change (w α) B = 0
      rw [hoff α hnot]
      rfl)
  rw [hsum]
  apply MeasureTheory.Measure.sum_apply_eq_zero.mpr
  intro α
  exact (_root_.MeasureTheory.withDensity_absolutelyContinuous
    (chartLocalMeasure (I := I) g α.val)
    (fun x : M => ENNReal.ofReal (ρ α.val x))) (hA α.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure ``Submission.DifferentialGeometry.Geometry.Measure.riemannianMeasure_null_of_chartLocalMeasure

end DifferentialGeometry.Geometry.Measure

end
