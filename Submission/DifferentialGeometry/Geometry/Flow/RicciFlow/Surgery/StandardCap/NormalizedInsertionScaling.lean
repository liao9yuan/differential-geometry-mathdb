import Submission.DifferentialGeometry.Geometry.Neck.Scaling
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ModelWindow
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.QuotientCollapse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.E3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientIsManifold target :: scope.openDecls } }
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientT2Space target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instNeZeroNatFinrankReal : NeZero (Module.finrank ℝ E) := ⟨by rw [show Module.finrank ℝ E = 3 from Fact.out]; decide⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instNeZeroNatFinrankReal
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instNeZeroNatFinrankReal target :: scope.openDecls } }

theorem rescaled_positiveRetainedMap (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).positiveRetainedMap = d.positiveRetainedMap := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveRetainedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveRetainedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveRetainedMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveRetainedMap

theorem rescaled_positiveSideInsertionMetric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (d.rescaled c hc).positiveSideInsertionMetric hA hAB =
      scaleMetric c hc (d.positiveSideInsertionMetric hA hAB) := by
  have he : insertedQuotientMetric hA hAB (d.rescaled c hc).controlledMetric_cylinder_lower.1
      (d.rescaled c hc).controlledMetric =
      insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric := by
    exact congrArg (fun h => insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 h)
      (d.rescaled_controlledMetric c hc)
  apply SmoothRiemannianMetric.ext_inner
  intro p u v
  change (metricScalarAt (scaleMetric c hc g) x₀)⁻¹ *
    (insertedQuotientMetric hA hAB (d.rescaled c hc).controlledMetric_cylinder_lower.1
      (d.rescaled c hc).controlledMetric).inner p u v =
      c * ((metricScalarAt g x₀)⁻¹ *
        (insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric).inner p u v)
  rw [he, metricScalarAt_scaleMetric]
  field_simp [hc.ne', d.scalar_pos.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideInsertionMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideInsertionMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideInsertionMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideInsertionMetric

theorem rescaled_positiveSideQuotientCollapseMap (d : normalizedDatum g x₀ δ k)
    (c : ℝ) (hc : 0 < c) {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (x : d.controlledImage) :
    (d.rescaled c hc).positiveSideQuotientCollapseMap hA hAB x =
      d.positiveSideQuotientCollapseMap hA hAB x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideQuotientCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideQuotientCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideQuotientCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_positiveSideQuotientCollapseMap

theorem rescaled_modelWindowPullback (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c)
    {A R : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (hfit : R ≤ transitionEnd + δ⁻¹) :
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (d.rescaled c hc).scalar_pos
        ((d.rescaled c hc).positiveSideInsertionMetric hA hAB)) =
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)) := by
  rw [normalizedDatum_modelWindowPullback, normalizedDatum_modelWindowPullback]
  exact congrArg (fun h => (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 h).restrictOpenOfSubset
    (modelWindow_le_insertionBall hfit)) (d.rescaled_controlledMetric c hc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_modelWindowPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_modelWindowPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_modelWindowPullback ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_modelWindowPullback

end DifferentialGeometry.Geometry.Neck.normalizedDatum
