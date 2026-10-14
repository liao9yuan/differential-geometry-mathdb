import Submission.DifferentialGeometry.Geometry.Neck.Naturality
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
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap _root_.Submission.DifferentialGeometry.Geometry.Metric
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Geometry.Neck.datumIsometry
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.E3 target :: scope.openDecls } }
private abbrev Retained (δ : ℝ) := Metric.sphere (0 : E3) 1 × _root_.Set.Ico (0 : ℝ) δ⁻¹

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.Retained target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.quotientIsManifold target :: scope.openDecls } }
private local instance quotientT2Space {B : ℝ} {hB : 0 < B} :
    T2Space (InsertionQuotient hB) := radialCapAttachment_t2Space transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.quotientT2Space
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.datumIsometry.quotientT2Space target :: scope.openDecls } }
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (Module.finrank ℝ E' = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

theorem positiveSideInsertionMetric_eq (F : datumIsometry d d')
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    d'.positiveSideInsertionMetric hA hAB = d.positiveSideInsertionMetric hA hAB := by
  have he : insertedQuotientMetric hA hAB d'.controlledMetric_cylinder_lower.1 d'.controlledMetric =
      insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric :=
    congrArg (fun h => insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 h)
      F.controlledMetric_eq
  apply SmoothRiemannianMetric.ext_inner
  intro p u v
  change (metricScalarAt g' x₀')⁻¹ *
    (insertedQuotientMetric hA hAB d'.controlledMetric_cylinder_lower.1 d'.controlledMetric).inner p u v =
    (metricScalarAt g x₀)⁻¹ *
    (insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric).inner p u v
  rw [F.scalar_eq, he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideInsertionMetric_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideInsertionMetric_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideInsertionMetric_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideInsertionMetric_eq

theorem modelWindowPullback_eq (F : datumIsometry d d')
    {A R : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (hfit : R ≤ transitionEnd + δ⁻¹) :
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g' x₀') d'.scalar_pos (d'.positiveSideInsertionMetric hA hAB)) =
    modelWindowPullback (inv_pos.mpr d.precision_pos) hfit
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)) := by
  rw [normalizedDatum_modelWindowPullback, normalizedDatum_modelWindowPullback]
  exact congrArg (fun h => (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 h).restrictOpenOfSubset
    (modelWindow_le_insertionBall hfit)) F.controlledMetric_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.modelWindowPullback_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.modelWindowPullback_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.modelWindowPullback_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.modelWindowPullback_eq

theorem controlledMap_mem_source (F : datumIsometry d d') (q : openCylinder δ⁻¹) :
    d.controlledMap q ∈ F.source :=
  F.image_source (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_mem_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_mem_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_mem_source ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_mem_source

theorem controlledMap_eq (F : datumIsometry d d') (q : openCylinder δ⁻¹) :
    (F.equiv ⟨d.controlledMap q, F.controlledMap_mem_source q⟩ : N) = d'.controlledMap q :=
  F.chart_eq (Opens.inclusion (openCylinder_inv_le_bufferedCylinder δ) q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.controlledMap_eq

theorem positiveRetainedMap_mem_source (F : datumIsometry d d') (q : Retained δ) :
    d.positiveRetainedMap q ∈ F.source := by
  rw [normalizedDatum.positiveRetainedMap_apply]
  exact F.image_source _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_mem_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_mem_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_mem_source ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_mem_source

theorem positiveRetainedMap_eq (F : datumIsometry d d') (q : Retained δ) :
    (F.equiv ⟨d.positiveRetainedMap q, F.positiveRetainedMap_mem_source q⟩ : N) =
      d'.positiveRetainedMap q := by
  let z : bufferedCylinder δ := ⟨(q.1, q.2.val), by
    change -δ⁻¹ - 1 < q.2.val ∧ q.2.val < δ⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr d.precision_pos, q.2.property.1, q.2.property.2]⟩
  have hs : (⟨d.positiveRetainedMap q, F.positiveRetainedMap_mem_source q⟩ : F.source) =
      ⟨d.map z, F.image_source z⟩ := Subtype.ext (d.positiveRetainedMap_apply q)
  exact (congrArg (fun x : F.source => (F.equiv x : N)) hs).trans
    ((F.chart_eq z).trans (d'.positiveRetainedMap_apply q).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.positiveRetainedMap_eq

theorem controlledImage_le_source (F : datumIsometry d d') : d.controlledImage ≤ F.source := by
  rintro p ⟨q, rfl⟩
  exact F.controlledMap_mem_source q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImage_le_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImage_le_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImage_le_source ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImage_le_source

def controlledImageMap (F : datumIsometry d d') : d.controlledImage → d'.controlledImage :=
  fun p => ⟨(F.equiv ⟨p.val, F.controlledImage_le_source p.property⟩ : N), by
    obtain ⟨q, hq⟩ := p.property
    have he : (F.equiv ⟨p.val, F.controlledImage_le_source p.property⟩ : N) = d'.controlledMap q := by
      have hp : (⟨p.val, F.controlledImage_le_source p.property⟩ : F.source) =
          ⟨d.controlledMap q, F.controlledMap_mem_source q⟩ := Subtype.ext hq.symm
      exact (congrArg (fun x : F.source => (F.equiv x : N)) hp).trans (F.controlledMap_eq q)
    rw [he]
    exact d'.controlledMap_mem_controlledImage q⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImageMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImageMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImageMap ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.controlledImageMap

theorem positiveSideQuotientCollapseMap_eq (F : datumIsometry d d')
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p : d.controlledImage) :
    d'.positiveSideQuotientCollapseMap hA hAB (F.controlledImageMap p) =
      d.positiveSideQuotientCollapseMap hA hAB p := by
  obtain ⟨q, hq⟩ := p.property
  have hp : p = ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ :=
    Subtype.ext hq.symm
  subst p
  have he : F.controlledImageMap ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ =
      ⟨d'.controlledMap q, d'.controlledMap_mem_controlledImage q⟩ :=
    Subtype.ext (F.controlledMap_eq q)
  rw [he, normalizedDatum.positiveSideQuotientCollapseMap_controlledMap,
    normalizedDatum.positiveSideQuotientCollapseMap_controlledMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideQuotientCollapseMap_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideQuotientCollapseMap_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideQuotientCollapseMap_eq ``Submission.DifferentialGeometry.Geometry.Neck.datumIsometry.positiveSideQuotientCollapseMap_eq

end DifferentialGeometry.Geometry.Neck.datumIsometry
