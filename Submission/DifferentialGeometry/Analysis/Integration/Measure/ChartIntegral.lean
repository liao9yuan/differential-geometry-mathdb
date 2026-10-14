import Submission.DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.Decomposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.Measure.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (alpha : M)
    {f : M → F} (hf : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt H alpha).source) :
    ∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ x, f x ∂chartLocalMeasure g alpha := by
  have hzero (x : M) (hx : x ∉ tsupport f) : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [← _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    riemannianVolumeMeasure_restrict_eq_chartLocalMeasure_restrict g alpha hf hs,
    _root_.MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset ``Submission.DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset

theorem integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
    [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M) (alpha : M)
    {f : M → Real} (hf : HasCompactSupport f) (hs : tsupport f ⊆ (chartAt H alpha).source)
    (hm : _root_.MeasureTheory.AEStronglyMeasurable f (chartLocalMeasure g alpha)) :
    ∫ x, f x ∂riemannianVolumeMeasure (I := I) (M := M) g =
      ∫ y in (extChartAt I alpha).target,
        chartDensity g alpha ((extChartAt I alpha).symm y) * f ((extChartAt I alpha).symm y)
        ∂modelHaar := by
  rw [integral_riemannianVolumeMeasure_eq_chartLocalMeasure_of_tsupport_subset g alpha hf hs]
  exact integral_chart_ae g alpha f hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset ``Submission.DifferentialGeometry.Integral.Measure.integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset

end DifferentialGeometry.Integral.Measure
