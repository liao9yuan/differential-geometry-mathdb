import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedCollapse

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Filter _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.S2 target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.IC target :: scope.openDecls } }
private abbrev Retained (δ : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) δ⁻¹

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.Retained target :: scope.openDecls } }
private abbrev Cap := {x : E3 // ‖x‖ ≤ transitionEnd}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.Cap target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) :=
  radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) :=
  radialCapAttachment_isManifold transitionEnd_pos hB

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
private local instance quotientRegularSpace {B : ℝ} {hB : 0 < B} :
    RegularSpace (InsertionQuotient hB) :=
  (radialCapAttachmentHomeomorph transitionEnd_pos hB).isEmbedding.isInducing.regularSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientRegularSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.quotientRegularSpace target :: scope.openDecls } }

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance _root_.Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instRegularSpaceSubtypeMemOpensControlledImage (d : normalizedDatum g x₀ δ k) : RegularSpace d.controlledImage :=
  d.controlledChart.symm.toHomeomorph.isEmbedding.isInducing.regularSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.instRegularSpaceSubtypeMemOpensControlledImage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.instRegularSpaceSubtypeMemOpensControlledImage target :: scope.openDecls } }

theorem positiveSideInsertionMetric_eq_pullback_collapseMetric (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    d.positiveSideInsertionMetric hA hAB = Diffeomorph.pullbackMetricCross
      (d.positiveSideCollapseMetric hA hAB)
      (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  erw [Diffeomorph.pullbackMetricCross_inner]
  simp only [positiveSideInsertionMetric, positiveSideCollapseMetric,
    scaleMetric_inner, insertedQuotientMetric_inner]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_eq_pullback_collapseMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_eq_pullback_collapseMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_eq_pullback_collapseMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_eq_pullback_collapseMetric

theorem positiveSideInsertionMetric_edist (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹)
    (p q : InsertionQuotient (inv_pos.mpr d.precision_pos)) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    riemannianEDistOf (d.positiveSideInsertionMetric hA hAB) p q =
      riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos) p)
        (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos) q) := by
  rw [positiveSideInsertionMetric_eq_pullback_collapseMetric]
  exact edistOf_pullbackMetricCross _ _ p q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_edist ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_edist

def positiveSideQuotientCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    d.controlledImage → InsertionQuotient (inv_pos.mpr d.precision_pos) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).symm ∘
    d.positiveSideCollapseMap hA hAB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap

theorem positiveSideQuotientCollapseMap_realization (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p : d.controlledImage) :
    radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)
      (d.positiveSideQuotientCollapseMap hA hAB p) = d.positiveSideCollapseMap hA hAB p :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).apply_symm_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_realization ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_realization

theorem positiveSideQuotientCollapseMap_controlledMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹) :
    d.positiveSideQuotientCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ =
        (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).symm
          (collapseMap hA hAB q) := by
  exact congrArg
    (fun x : insertionBall δ⁻¹ =>
      (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).symm x)
    (d.positiveSideCollapseMap_controlledMap hA hAB q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_controlledMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_controlledMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_controlledMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_controlledMap

theorem positiveRetainedMap_mem_controlledImage (d : normalizedDatum g x₀ δ k)
    (q : Retained δ) : d.positiveRetainedMap q ∈ d.controlledImage :=
  d.controlledMap_mem_controlledImage
    ⟨(q.1, q.2.val), ⟨by linarith [inv_pos.mpr d.precision_pos, q.2.property.1], q.2.property.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_mem_controlledImage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_mem_controlledImage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_mem_controlledImage ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_mem_controlledImage

theorem positiveSideQuotientCollapseMap_retained (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : Retained δ) :
    d.positiveSideQuotientCollapseMap hA hAB
      ⟨d.positiveRetainedMap q, d.positiveRetainedMap_mem_controlledImage q⟩ =
        adjunctionLower (i := radialCapBoundary transitionEnd_pos)
          (retainedBoundary (inv_pos.mpr d.precision_pos)) q := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).injective
  erw [positiveSideQuotientCollapseMap_realization]
  apply Subtype.ext
  exact d.positiveSideCollapseMap_retained hA hAB
    ⟨(q.1, q.2.val), ⟨by linarith [inv_pos.mpr d.precision_pos, q.2.property.1], q.2.property.2⟩⟩
    q.2.property.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_retained ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_retained

theorem positiveSideQuotientCollapseMap_collapsed (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹)
    (hq : q.val.2 ≤ collapseTip A) :
    d.positiveSideQuotientCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ =
        adjunctionCell (radialCapBoundary transitionEnd_pos)
          (retainedBoundary (inv_pos.mpr d.precision_pos))
          ⟨0, by simpa using transitionEnd_pos.le⟩ := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).injective
  erw [positiveSideQuotientCollapseMap_realization]
  apply Subtype.ext
  exact d.positiveSideCollapseMap_collapsed hA hAB q hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_collapsed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_collapsed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_collapsed ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_collapsed

private theorem collapseRadialPoint_mem_cap {A : ℝ} (hA : 0 < A)
    (y : S2) (z : ℝ) (hz : z ∈ _root_.Set.Icc (collapseTip A) 0) :
    ‖collapseRadius A z • (y : E3)‖ ≤ transitionEnd := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (collapseRadius_mapsTo hA hz).1,
    mem_sphere_zero_iff_norm.mp y.property, mul_one]
  exact (collapseRadius_mapsTo hA hz).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.collapseRadialPoint_mem_cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.collapseRadialPoint_mem_cap target :: scope.openDecls } }

theorem positiveSideQuotientCollapseMap_radial (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹)
    (hq : q.val.2 ∈ _root_.Set.Icc (collapseTip A) 0) :
    d.positiveSideQuotientCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ =
        adjunctionCell (radialCapBoundary transitionEnd_pos)
          (retainedBoundary (inv_pos.mpr d.precision_pos))
          ⟨collapseRadius A q.val.2 • (q.val.1 : E3), collapseRadialPoint_mem_cap hA _ _ hq⟩ := by
  apply (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).injective
  erw [positiveSideQuotientCollapseMap_realization]
  apply Subtype.ext
  exact d.positiveSideCollapseMap_radial hA hAB q hq.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_radial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_radial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_radial ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_radial

theorem continuous_positiveSideQuotientCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    Continuous (d.positiveSideQuotientCollapseMap hA hAB) :=
  (radialCapAttachmentDiffeomorph transitionEnd_pos (inv_pos.mpr d.precision_pos)).symm.contMDiff.continuous.comp
    (d.continuous_positiveSideCollapseMap hA hAB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideQuotientCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideQuotientCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideQuotientCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.continuous_positiveSideQuotientCollapseMap

theorem positiveSideQuotientCollapseMap_edist (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p q : d.controlledImage) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    riemannianEDistOf (d.positiveSideInsertionMetric hA hAB)
      (d.positiveSideQuotientCollapseMap hA hAB p) (d.positiveSideQuotientCollapseMap hA hAB q) =
      riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB p) (d.positiveSideCollapseMap hA hAB q) := by
  rw [positiveSideInsertionMetric_edist, positiveSideQuotientCollapseMap_realization,
    positiveSideQuotientCollapseMap_realization]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_edist ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_edist

theorem positiveSideQuotientCollapseMap_local_intrinsic_bound (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p : d.controlledImage) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf (d.positiveSideInsertionMetric hA hAB)
        (d.positiveSideQuotientCollapseMap hA hAB x) (d.positiveSideQuotientCollapseMap hA hAB y) ≤
          L * riemannianEDistOf (g.restrictOpen d.controlledImage) x y := by
  obtain ⟨L, t, ht, hL⟩ := d.positiveSideCollapseMap_local_intrinsic_bound hA hAB p
  refine ⟨L, t, ht, ?_⟩
  intro x hx y hy
  rw [positiveSideQuotientCollapseMap_edist]
  exact hL x hx y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_local_intrinsic_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_local_intrinsic_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_local_intrinsic_bound ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_local_intrinsic_bound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isometry_positiveSideInsertion_realization (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (let hB := inv_pos.mpr d.precision_pos
     letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
     let s := d.positiveSideInsertionMetric hA hAB
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) := ⟨s.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) :=
       ⟨s.inner, s.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace (InsertionQuotient hB) := .ofRiemannianMetric (𝓡 3) (InsertionQuotient hB)
     let h := d.positiveSideCollapseMetric hA hAB
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace (insertionBall δ⁻¹) := .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
     @Isometry (InsertionQuotient hB) (insertionBall δ⁻¹) inferInstance inferInstance
       (radialCapAttachmentDiffeomorph transitionEnd_pos hB)) := by
  dsimp only
  intro p q
  exact (d.positiveSideInsertionMetric_edist hA hAB p q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.isometry_positiveSideInsertion_realization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.isometry_positiveSideInsertion_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.isometry_positiveSideInsertion_realization ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.isometry_positiveSideInsertion_realization

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitz_positiveSideQuotientCollapseMap (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (let hB := inv_pos.mpr d.precision_pos
     letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
     let s := g.restrictOpen d.controlledImage
     letI : _root_.Bundle.RiemannianBundle (TangentSpace I : d.controlledImage → Type _) := ⟨s.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
       ⟨s.inner, s.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace d.controlledImage := .ofRiemannianMetric I d.controlledImage
     let h := d.positiveSideInsertionMetric hA hAB
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace (InsertionQuotient hB) := .ofRiemannianMetric (𝓡 3) (InsertionQuotient hB)
     LocallyLipschitz (d.positiveSideQuotientCollapseMap hA hAB)) :=
  (locallyLipschitz_iff_local_riemannianEDistOf_le (g.restrictOpen d.controlledImage)
    (d.positiveSideInsertionMetric hA hAB) (d.positiveSideQuotientCollapseMap hA hAB)).mpr
      (d.positiveSideQuotientCollapseMap_local_intrinsic_bound hA hAB)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideQuotientCollapseMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideQuotientCollapseMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideQuotientCollapseMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.locallyLipschitz_positiveSideQuotientCollapseMap

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem positiveSideQuotientCollapseMap_eVariationOn_le (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (γ : ℝ → d.controlledImage)
    (a b : ℝ) (hγ : ContinuousOn γ (_root_.Set.Icc a b)) :
    (let hB := inv_pos.mpr d.precision_pos
     letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
     let s := g.restrictOpen d.controlledImage
     letI : _root_.Bundle.RiemannianBundle (TangentSpace I : d.controlledImage → Type _) := ⟨s.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
       ⟨s.inner, s.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace d.controlledImage := .ofRiemannianMetric I d.controlledImage
     let h := d.positiveSideInsertionMetric hA hAB
     letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) := ⟨h.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) :=
       ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
     letI : PseudoEMetricSpace (InsertionQuotient hB) := .ofRiemannianMetric (𝓡 3) (InsertionQuotient hB)
     eVariationOn (d.positiveSideQuotientCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) ≤ eVariationOn γ (_root_.Set.Icc a b)) := by
  let hB := inv_pos.mpr d.precision_pos
  let s := g.restrictOpen d.controlledImage
  let h := d.positiveSideInsertionMetric hA hAB
  let v := d.positiveSideCollapseMetric hA hAB
  let mi : PseudoEMetricSpace d.controlledImage := by
    letI : _root_.Bundle.RiemannianBundle (TangentSpace I : d.controlledImage → Type _) := ⟨s.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
      ⟨s.inner, s.contMDiff.continuous, fun _ _ _ => rfl⟩
    exact .ofRiemannianMetric I d.controlledImage
  let mq : PseudoEMetricSpace (InsertionQuotient hB) := by
    letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) := ⟨h.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : InsertionQuotient hB → Type _) :=
      ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
    exact .ofRiemannianMetric (𝓡 3) (InsertionQuotient hB)
  let mb : PseudoEMetricSpace (insertionBall δ⁻¹) := by
    letI : _root_.Bundle.RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) := ⟨v.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      ⟨v.inner, v.contMDiff.continuous, fun _ _ _ => rfl⟩
    exact .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
  have hb := d.positiveSideCollapseMap_eVariationOn_le hA hAB γ a b hγ
  change @eVariationOn ℝ _ (insertionBall δ⁻¹) mb
    (d.positiveSideCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) ≤
      @eVariationOn ℝ _ d.controlledImage mi γ (_root_.Set.Icc a b) at hb
  have he : @eVariationOn ℝ _ (InsertionQuotient hB) mq
      (d.positiveSideQuotientCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) =
      @eVariationOn ℝ _ (insertionBall δ⁻¹) mb
        (d.positiveSideCollapseMap hA hAB ∘ γ) (_root_.Set.Icc a b) := by
    unfold eVariationOn
    apply iSup_congr
    intro p
    apply Finset.sum_congr rfl
    intro i _
    exact d.positiveSideQuotientCollapseMap_edist hA hAB (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
  exact he.trans_le hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_eVariationOn_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_eVariationOn_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_eVariationOn_le ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideQuotientCollapseMap_eVariationOn_le

end DifferentialGeometry.Geometry.Neck.normalizedDatum
