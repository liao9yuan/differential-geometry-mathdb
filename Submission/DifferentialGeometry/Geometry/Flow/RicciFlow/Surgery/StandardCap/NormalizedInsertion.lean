import Submission.DifferentialGeometry.Geometry.Neck.InsertionInput
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
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
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.IR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.IR target :: scope.openDecls } }
private abbrev Retained (δ : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) δ⁻¹

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.Retained
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.Retained target :: scope.openDecls } }
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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

def positiveRetainedMap (d : normalizedDatum g x₀ δ k) : Retained δ → M :=
  fun q => d.controlledMap ⟨(q.1, q.2.val),
    ⟨by linarith [inv_pos.mpr d.precision_pos, q.2.property.1], q.2.property.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap

def positiveSideInsertionMetric (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    letI := radialCapAttachmentChartedSpace transitionEnd_pos (inv_pos.mpr d.precision_pos)
    SmoothRiemannianMetric (𝓡 3) (InsertionQuotient (inv_pos.mpr d.precision_pos)) :=
  scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos)
    (insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric

theorem positiveSideInsertionMetric_normalization (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB) =
      insertedQuotientMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [positiveSideInsertionMetric, scaleMetric_inner]
  rw [← mul_assoc, mul_inv_cancel₀ d.scalar_pos.ne', one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_normalization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_normalization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_normalization ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_normalization

theorem positiveRetainedMap_apply (d : normalizedDatum g x₀ δ k) (q : Retained δ) :
    d.positiveRetainedMap q = d.map ⟨(q.1, q.2.val), ⟨by
      change -δ⁻¹ - 1 < q.2.val
      linarith [inv_pos.mpr d.precision_pos, q.2.property.1], by
      change q.2.val < δ⁻¹ + 1
      linarith [q.2.property.2]⟩⟩ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_apply ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_apply

private def retainedIntoControlled (d : normalizedDatum g x₀ δ k) :
    Retained δ → openCylinder δ⁻¹ :=
  fun q => ⟨(q.1, q.2.val),
    ⟨by linarith [inv_pos.mpr d.precision_pos, q.2.property.1], q.2.property.2⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedIntoControlled
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedIntoControlled target :: scope.openDecls } }

private theorem retainedIntoControlled_smooth (d : normalizedDatum g x₀ δ k) :
    letI := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
    ContMDiff IR IC ∞ d.retainedIntoControlled := by
  let hB := inv_pos.mpr d.precision_pos
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  intro q
  exact codRestr_contMDiffAt (I := IR) (J := IC) (V := openCylinder δ⁻¹)
    (fun p => (d.retainedIntoControlled p).property)
    (contMDiff_fst.prodMk
      ((isSmoothEmbedding_halfClosedInterval_inclusion hB).contMDiff.comp contMDiff_snd)).contMDiffAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedIntoControlled_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.retainedIntoControlled_smooth target :: scope.openDecls } }

theorem positiveRetainedMap_smooth (d : normalizedDatum g x₀ δ k) :
    letI := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
    ContMDiff IR I ∞ d.positiveRetainedMap := by
  let := halfClosedIntervalChartedSpace (inv_pos.mpr d.precision_pos)
  let := halfClosedInterval_isManifold (inv_pos.mpr d.precision_pos)
  exact d.controlledMap_smooth.comp d.retainedIntoControlled_smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_smooth ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveRetainedMap_smooth

theorem positiveSideInsertionMetric_retained (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    let hB := inv_pos.mpr d.precision_pos
    letI := halfClosedIntervalChartedSpace hB
    ∀ (q : Retained δ) (v w : TangentSpace IR q),
      (d.positiveSideInsertionMetric hA hAB).inner
        (adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB) q)
        (mfderiv IR (𝓡 3)
          (adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) q v)
        (mfderiv IR (𝓡 3)
          (adjunctionLower (i := radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) q w) =
      g.inner (d.positiveRetainedMap q)
        (mfderiv IR I d.positiveRetainedMap q v)
        (mfderiv IR I d.positiveRetainedMap q w) := by
  let hB := inv_pos.mpr d.precision_pos
  let := halfClosedIntervalChartedSpace hB
  let := halfClosedInterval_isManifold hB
  dsimp only
  intro q v w
  let ρ := d.retainedIntoControlled
  have hρ : ContMDiff IR IC ∞ ρ := d.retainedIntoControlled_smooth
  have hcoord (u : TangentSpace IR q) :
      mfderiv IR IC ρ q u =
        mfderiv IR IC (fun p : Retained δ => (p.1, p.2.val)) q u := by
    have hh := mfderiv_comp q
      ((contMDiff_subtype_val (I := IC) (U := openCylinder δ⁻¹) (n := ∞)).mdifferentiableAt (by decide))
      (hρ.mdifferentiableAt (by decide))
    rw [mfderiv_subtype_val] at hh
    exact (congrArg (fun D => D u) hh).symm
  have htotal (u : TangentSpace IR q) :
      mfderiv IR I d.positiveRetainedMap q u =
        mfderiv IC I d.controlledMap (ρ q)
          (mfderiv IR IC (fun p : Retained δ => (p.1, p.2.val)) q u) := by
    have hh := mfderiv_comp q (d.controlledMap_smooth.mdifferentiableAt (by decide))
      (hρ.mdifferentiableAt (by decide))
    have hu := congrArg (fun D => D u) hh
    rw [ContinuousLinearMap.comp_apply, hcoord] at hu
    exact hu
  simp only [positiveSideInsertionMetric, scaleMetric_inner]
  erw [insertedQuotientMetric_retained, controlledMetric_inner, htotal, htotal]
  rw [← mul_assoc, inv_mul_cancel₀ d.scalar_pos.ne', one_mul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_retained then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_retained"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_retained ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_retained

theorem positiveSideInsertionMetric_cap_of_inner (d : normalizedDatum g x₀ δ k)
    {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    let hB := inv_pos.mpr d.precision_pos
    letI := closedBallChartedSpace transitionEnd_pos
    ∀ (x : {x : E3 // ‖x‖ ≤ transitionEnd}), ‖x.val‖ < conformalRadius (-7 * A / 4) →
      ∀ (v w : TangentSpace (𝓡∂ 3) x),
      (d.positiveSideInsertionMetric hA hAB).inner
        (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x)
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3)
          (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x w) =
      ((1 - Real.sqrt δ) / metricScalarAt g x₀) * metric.inner x.val
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : {x : E3 // ‖x‖ ≤ transitionEnd} → E3) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : {x : E3 // ‖x‖ ≤ transitionEnd} → E3) x w) := by
  let := closedBallChartedSpace transitionEnd_pos
  dsimp only
  intro x hx v w
  simp only [positiveSideInsertionMetric, scaleMetric_inner]
  rw [insertedQuotientMetric_cap_of_inner _ _ _ _ x hx]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_cap_of_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_cap_of_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_cap_of_inner ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.positiveSideInsertionMetric_cap_of_inner

end DifferentialGeometry.Geometry.Neck.normalizedDatum
