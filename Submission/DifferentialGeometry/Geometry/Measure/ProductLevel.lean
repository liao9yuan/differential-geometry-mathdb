import Submission.DifferentialGeometry.Geometry.Measure.ChartVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Measure
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceProdReal_differentialGeometry : MeasurableSpace (E × ℝ) := borel (E × ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceProdReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpaceProdReal_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceProdReal_differentialGeometry : BorelSpace (E × ℝ) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceProdReal_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpaceProdReal_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceSubtypeProdRealMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens (M × ℝ)) : MeasurableSpace U := borel U

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpaceSubtypeProdRealMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpaceSubtypeProdRealMemOpens_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceSubtypeProdRealMemOpens_differentialGeometry (U : _root_.TopologicalSpace.Opens (M × ℝ)) : BorelSpace U := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpaceSubtypeProdRealMemOpens_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpaceSubtypeProdRealMemOpens_differentialGeometry target :: scope.openDecls } }

private theorem modelHaar_snd_fiber_eq_zero (c : ℝ) :
    modelHaar (E := E × ℝ) {x | x.2 = c} = 0 := by
  let K : Submodule ℝ (E × ℝ) := (LinearMap.snd ℝ E ℝ).ker
  have hproper : K ≠ ⊤ := by
    intro h
    have hm : ((0 : E), (1 : ℝ)) ∈ K := by rw [h]; trivial
    simp [K] at hm
  have hzero := MeasureTheory.Measure.addHaar_submodule (modelHaar (E := E × ℝ)) K hproper
  have hset : {x : E × ℝ | x.2 = c} =
      (fun x : E × ℝ => x + (0, -c)) ⁻¹' (K : Set (E × ℝ)) := by
    ext x
    simp [K, ← sub_eq_add_neg, sub_eq_zero]
  rw [hset, _root_.MeasureTheory.measure_preimage_add_right, hzero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.modelHaar_snd_fiber_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.modelHaar_snd_fiber_eq_zero target :: scope.openDecls } }

theorem riemannianVolumeMeasure_snd_fiber_eq_zero
    [T2Space M] (U : _root_.TopologicalSpace.Opens (M × ℝ)) [SigmaCompactSpace U]
    (g : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) U) (c : ℝ) :
    riemannianVolumeMeasure (I.prod 𝓘(ℝ)) U g {x | x.val.2 = c} = 0 := by
  apply riemannianVolumeMeasure_eq_zero_of_chart_preimages g
    ((isClosed_eq (continuous_snd.comp continuous_subtype_val) continuous_const).measurableSet)
  intro α
  apply _root_.MeasureTheory.measure_mono_null _ (modelHaar_snd_fiber_eq_zero (E := E) c)
  rintro u ⟨hu, ht⟩
  have heq := congrArg Prod.snd ((extChartAt (I.prod 𝓘(ℝ)) α).right_inv ht)
  change ((extChartAt (I.prod 𝓘(ℝ)) α).symm u).val.2 = u.2 at heq
  change u.2 = c
  exact heq.symm.trans hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_snd_fiber_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_snd_fiber_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_snd_fiber_eq_zero ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_snd_fiber_eq_zero
end DifferentialGeometry.Geometry.Measure
