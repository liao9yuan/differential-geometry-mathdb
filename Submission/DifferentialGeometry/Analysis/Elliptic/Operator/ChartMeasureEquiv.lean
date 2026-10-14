import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.Support
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Basic
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.Matrix _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartMeasureEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in (extChartAt I α).target,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y)
        ∂(modelHaar (E := E)) := by
  classical
  have hf_int := integrable_chartLocalMeasure_of_compactSupport_subset_chartSource
    (I := I) (M := M) g α hf_cont hf_cs hf_support
  have h_step1 :=
    (integrable_riemannianVolumeMeasure_and_integral_eq_chartLocalMeasure
      (I := I) (M := M) g α hf_int hf_cs hf_support).2
  rw [h_step1]
  exact integral_chartLocalMeasure (I := I) (M := M) g α f hf_cont.measurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in (extChartAt I α).target,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y)
        ∂(modelHaar (E := E)) :=
  integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont (HasCompactSupport.of_compactSpace f) hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) *
          Set.indicator (extChartAt I α).target (fun _ => (1 : ℝ)) y
        ∂(modelHaar (E := E)) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont hf_cs hf_support]
  have htgt_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htgt_meas).symm]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator_of_hasCompactSupport

theorem integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) *
          Set.indicator (extChartAt I α).target (fun _ => (1 : ℝ)) y
        ∂(modelHaar (E := E)) := by
  exact integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont (HasCompactSupport.of_compactSpace f) hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_indicator

private def toEuclideanMeasurableEquiv :
    E ≃ᵐ EuclN :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclideanMeasurableEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclideanMeasurableEquiv target :: scope.openDecls } }

@[simp] private lemma toEuclideanMeasurableEquiv_apply (y : E) :
    toEuclideanMeasurableEquiv (E := E) y = toEuclidean y := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclideanMeasurableEquiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclideanMeasurableEquiv_apply target :: scope.openDecls } }

@[simp] private lemma toEuclideanMeasurableEquiv_symm_apply (y : EuclN) :
    (toEuclideanMeasurableEquiv (E := E)).symm y = (toEuclidean (E := E)).symm y := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclideanMeasurableEquiv_symm_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclideanMeasurableEquiv_symm_apply target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma toEuclidean_mem_chartTargetEuclid_iff
    (α : M) (y : E) :
    toEuclidean (E := E) y ∈ chartTargetEuclid (I := I) (M := M) α ↔
      y ∈ (extChartAt I α).target := by
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rcases hy with ⟨z, hz_target, hz_eq⟩
    have hyz : y = z := ((toEuclidean (E := E)).injective hz_eq).symm
    rw [hyz]; exact hz_target
  · exact ⟨y, hy, rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclidean_mem_chartTargetEuclid_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.toEuclidean_mem_chartTargetEuclid_iff target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma chartTargetEuclid_measurableSet (α : M) :
    MeasurableSet (chartTargetEuclid (I := I) (M := M) α) := by
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  change MeasurableSet (toEuclidean '' (extChartAt I α).target)
  exact (toEuclideanMeasurableEquiv (E := E)).measurableEmbedding.measurableSet_image.mpr
    htarget_meas

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.chartTargetEuclid_measurableSet
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.chartTargetEuclid_measurableSet target :: scope.openDecls } }

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_modelHaar_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont hf_cs hf_support]
  have htarget_meas : MeasurableSet (extChartAt I α).target :=
    measurableSet_extChartAt_target (I := I) α
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [show
      (∫ y in (extChartAt I α).target,
          chartDensity g α ((extChartAt I α).symm y) *
            f ((extChartAt I α).symm y)
          ∂(modelHaar (E := E))) =
        ∫ y, (extChartAt I α).target.indicator
              (fun y' : E =>
                chartDensity g α ((extChartAt I α).symm y') *
                  f ((extChartAt I α).symm y')) y
            ∂(modelHaar (E := E)) from
        (MeasureTheory.integral_indicator htarget_meas).symm]
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y',
            (chartTargetEuclid (I := I) (M := M) α).indicator
              (fun y'' : EuclN =>
                densityOnEuclid (I := I) g α y'' *
                  f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
            ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
                (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  rw [show
      (∫ y',
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y''))) y'
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y'' : EuclN =>
              densityOnEuclid (I := I) g α y'' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'')))
            (toEuclideanMeasurableEquiv (E := E) y)
          ∂(modelHaar (E := E)) from ?_]
  · refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun y => ?_))
    simp only
    by_cases hy : y ∈ (extChartAt I α).target
    · have hctE_y : toEuclideanMeasurableEquiv (E := E) y ∈
          chartTargetEuclid (I := I) (M := M) α :=
        (toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mpr hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hctE_y]
      have h_symm_apply :
          (toEuclidean (E := E)).symm (toEuclidean y) = y :=
        (toEuclidean (E := E)).symm_apply_apply y
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        densityOnEuclid (I := I) g α (toEuclidean y) *
          f ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y)))
      rw [h_symm_apply]
      change chartDensity g α ((extChartAt I α).symm y) *
          f ((extChartAt I α).symm y) =
        chartDensity g α ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm (toEuclidean y))) *
          f ((extChartAt I α).symm y)
      rw [h_symm_apply]
    · have hctE_off : toEuclideanMeasurableEquiv (E := E) y ∉
          chartTargetEuclid (I := I) (M := M) α := by
        intro hcontra
        exact hy ((toEuclidean_mem_chartTargetEuclid_iff (I := I) (M := M) α y).mp hcontra)
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hctE_off]
  · exact MeasureTheory.integral_map_equiv
      (μ := modelHaar (E := E))
      (e := toEuclideanMeasurableEquiv (E := E))
      (f := fun y'' : EuclN =>
        (chartTargetEuclid (I := I) (M := M) α).indicator
          (fun y''' : EuclN =>
            densityOnEuclid (I := I) g α y''' *
              f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'''))) y'')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) :=
  integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont (HasCompactSupport.of_compactSpace f) hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator_of_hasCompactSupport
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f) (hf_cs : HasCompactSupport f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          Set.indicator (chartTargetEuclid (I := I) (M := M) α)
            (fun _ => (1 : ℝ)) y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  classical
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont hf_cs hf_support]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_measurableSet (I := I) (M := M) α
  rw [show
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E)))) =
        ∫ y,
          (chartTargetEuclid (I := I) (M := M) α).indicator
            (fun y' : EuclN =>
              densityOnEuclid (I := I) g α y' *
                f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y'))) y
          ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
              (modelHaar (E := E))) from
        (MeasureTheory.integral_indicator hctE_meas).symm]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun y => ?_))
  simp only
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, mul_one]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator_of_hasCompactSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator_of_hasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator_of_hasCompactSupport ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator_of_hasCompactSupport

theorem integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf_cont : Continuous f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    ∫ x, f x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          f ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
          Set.indicator (chartTargetEuclid (I := I) (M := M) α)
            (fun _ => (1 : ℝ)) y
        ∂(MeasureTheory.Measure.map (toEuclidean : E → EuclN)
            (modelHaar (E := E))) := by
  exact integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator_of_hasCompactSupport
    (I := I) (M := M) g α hf_cont (HasCompactSupport.of_compactSpace f) hf_support

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv.integral_riemannianVolumeMeasure_eq_euclidean_chartTarget_indicator

end ChartMeasureEquiv
end Laplacian
end Analysis
end DifferentialGeometry
