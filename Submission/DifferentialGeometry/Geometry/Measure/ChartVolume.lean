import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Measure
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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

private theorem ae_chartLocalMeasure_mem_source
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ᵐ x ∂chartLocalMeasure g α, x ∈ (chartAt H α).source := by
  have hnull := chartLocalMeasure_apply_of_disjoint_source g α
    (chartAt H α).open_source.measurableSet.compl
    (show Disjoint ((chartAt H α).source)ᶜ (chartAt H α).source from disjoint_compl_left)
  simpa only [_root_.Set.mem_compl_iff, _root_.Classical.not_not] using measure_eq_zero_iff_ae_notMem.mp hnull

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.ae_chartLocalMeasure_mem_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.ae_chartLocalMeasure_mem_source target :: scope.openDecls } }

theorem chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (α : M) :
    chartLocalMeasure g α ≪ riemannianVolumeMeasure I M g := by
  intro N hN
  rw [_root_.MeasureTheory.measure_eq_zero_iff_ae_notMem]
  let ρ := chartAtlasPOU I M
  let S : Set M := {β : M | (Function.support (ρ β)).Nonempty}
  have : Countable S := (countable_nonempty_support_of_pou ρ).to_subtype
  have hglobal : ∀ᵐ x ∂riemannianVolumeMeasure I M g, x ∉ N :=
    measure_eq_zero_iff_ae_notMem.mp hN
  have hweighted (β : M) : ∀ᵐ x ∂chartLocalMeasure g β,
      ENNReal.ofReal (ρ β x) ≠ 0 → x ∉ N := by
    apply (_root_.MeasureTheory.ae_withDensity_iff (measurable_ofReal_pou_weight ρ β)).mp
    exact (Measure.absolutelyContinuous_of_le
      (chartLocalMeasure_withDensity_le_riemannianMeasure g ρ β)).ae_le hglobal
  have hlocal (β : S) : ∀ᵐ x ∂chartLocalMeasure g α,
      x ∈ (chartAt H α).source ∩ (chartAt H (β : M)).source →
        ENNReal.ofReal (ρ β x) ≠ 0 → x ∉ N := by
    apply (_root_.MeasureTheory.ae_restrict_iff' (measurableSet_chartAt_source_inter α (β : M))).mp
    rw [chartLocalMeasure_restrict_overlap_eq g α (β : M)]
    exact _root_.MeasureTheory.ae_restrict_of_ae (hweighted β)
  filter_upwards [ae_all_iff.mpr hlocal, ae_chartLocalMeasure_mem_source g α] with x hx hxs
  obtain ⟨β, hβ⟩ := ρ.exists_pos_of_mem (_root_.Set.mem_univ x)
  have hβsrc : x ∈ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β (subset_tsupport (ρ β) (ne_of_gt hβ))
  exact hx ⟨β, ⟨x, ne_of_gt hβ⟩⟩ ⟨hxs, hβsrc⟩
    (ne_of_gt (ENNReal.ofReal_pos.mpr hβ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Geometry.Measure.chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure

theorem ae_extChartAt_symm_of_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (α : M)
    {P : M → Prop} (hP : ∀ᵐ x ∂riemannianVolumeMeasure I M g, P x) :
    ∀ᵐ y ∂(modelHaar (E := E)).restrict (extChartAt I α).target,
      P ((extChartAt I α).symm y) := by
  have hlocal : ∀ᵐ x ∂chartLocalMeasure g α, P x :=
    (chartLocalMeasure_absolutelyContinuous_riemannianVolumeMeasure g α).ae_le hP
  have hdensity := aemeasurable_chartDensity_symm_pullback g α
  have hsymm := (aemeasurable_extChartAt_symm_restrict_target (I := I) α).mono_ac
    (_root_.MeasureTheory.withDensity_absolutelyContinuous _
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y))))
  have hpull := Measure.tendsto_ae_map hsymm hlocal
  have hcancel := (_root_.MeasureTheory.ae_withDensity_iff' hdensity).mp hpull
  filter_upwards [hcancel, _root_.MeasureTheory.ae_restrict_mem (measurableSet_extChartAt_target (I := I) α)] with y hy hyt
  apply hy
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (chartDensity_pos g α (by
      simpa only [trivializationAt_baseSet_eq_chartAt_source,
        extChartAt_source_eq_chartAt_source] using (extChartAt I α).map_target hyt)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.ae_extChartAt_symm_of_riemannianVolumeMeasure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.ae_extChartAt_symm_of_riemannianVolumeMeasure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.ae_extChartAt_symm_of_riemannianVolumeMeasure ``Submission.DifferentialGeometry.Geometry.Measure.ae_extChartAt_symm_of_riemannianVolumeMeasure

theorem riemannianVolumeMeasure_eq_zero_of_chart_preimages
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    {S : Set M} (hS : MeasurableSet S)
    (hchart : ∀ α : M, modelHaar (E := E)
      ((extChartAt I α).symm ⁻¹' S ∩ (extChartAt I α).target) = 0) :
    riemannianVolumeMeasure I M g S = 0 := by
  have hlocal (α : M) : chartLocalMeasure g α S = 0 := by
    unfold chartLocalMeasure
    have hac := _root_.MeasureTheory.withDensity_absolutelyContinuous
      ((modelHaar (E := E)).restrict (extChartAt I α).target)
      (fun y : E => ENNReal.ofReal (chartDensity g α ((extChartAt I α).symm y)))
    have hsymm := (aemeasurable_extChartAt_symm_restrict_target (I := I) α).mono_ac hac
    rw [Measure.map_apply_of_aemeasurable hsymm hS]
    apply hac
    rw [Measure.restrict_apply' (measurableSet_extChartAt_target (I := I) α)]
    exact hchart α
  rw [riemannianVolumeMeasure_def, riemannianMeasure_def,
    Measure.sum_apply_eq_zero' hS]
  intro α
  exact (_root_.MeasureTheory.withDensity_absolutelyContinuous (chartLocalMeasure g α)
    (fun x : M => ENNReal.ofReal (chartAtlasPOU I M α x))) (hlocal α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_eq_zero_of_chart_preimages then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_eq_zero_of_chart_preimages"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_eq_zero_of_chart_preimages ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_eq_zero_of_chart_preimages

end DifferentialGeometry.Geometry.Measure
