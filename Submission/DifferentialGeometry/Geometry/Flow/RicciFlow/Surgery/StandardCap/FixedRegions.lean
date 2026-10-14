import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.NormalizedInsertion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

def deepRadius (A : ℝ) : ℝ := _root_.Min.min 1 (_root_.Min.min transitionEnd (conformalRadius (-7 * A / 4))) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRadius

def positiveRadius (A : ℝ) : ℝ := deepRadius A / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRadius

def positiveRegion (A : ℝ) : Set E3 := {x | ‖x‖ ≤ positiveRadius A}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.positiveRegion

def deepRegion (A : ℝ) : Set E3 := {x | ‖x‖ ≤ deepRadius A}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRegion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRegion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRegion ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deepRegion

theorem fixed_radii_bounds (A : ℝ) :
    0 < positiveRadius A ∧ positiveRadius A < deepRadius A ∧
      deepRadius A < _root_.Min.min 1 transitionEnd ∧ deepRadius A < conformalRadius (-7 * A / 4) := by
  let R := _root_.Min.min 1 (_root_.Min.min transitionEnd (conformalRadius (-7 * A / 4)))
  have hR : 0 < R := lt_min zero_lt_one (lt_min transitionEnd_pos (conformalRadius_pos _))
  have hd : 0 < deepRadius A := half_pos hR
  refine ⟨half_pos hd, half_lt_self hd, ?_, ?_⟩
  · apply lt_min
    · exact (half_lt_self hR).trans_le (min_le_left _ _)
    · exact (half_lt_self hR).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  · exact (half_lt_self hR).trans_le ((min_le_right _ _).trans (min_le_right _ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_radii_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_radii_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_radii_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_radii_bounds

theorem fixed_regions_properties (A : ℝ) :
    IsCompact (positiveRegion A) ∧ IsCompact (deepRegion A) ∧
      positiveRegion A ⊆ deepRegion A ∧
      ∀ x ∈ positiveRegion A, ∀ u v : TangentSpace (𝓡 3) x,
        metric.inner x u u * metric.inner x v v - metric.inner x u v ^ 2 ≠ 0 →
          0 < sectionalCurvature metric x u v := by
  obtain ⟨_hp, hpd, hd, _hc⟩ := fixed_radii_bounds A
  have hpcompact : IsCompact (positiveRegion A) := by
    simpa only [positiveRegion, Metric.closedBall, dist_zero_right] using
      _root_.ProperSpace.isCompact_closedBall (0 : E3) (positiveRadius A)
  have hdcompact : IsCompact (deepRegion A) := by
    simpa only [deepRegion, Metric.closedBall, dist_zero_right] using
      _root_.ProperSpace.isCompact_closedBall (0 : E3) (deepRadius A)
  refine ⟨hpcompact, hdcompact, fun x hx => hx.trans hpd.le, ?_⟩
  intro x hx u v hplane
  have hxL : ‖x‖ < transitionEnd := (hx.trans_lt hpd).trans (hd.trans_le (min_le_right _ _))
  exact sectionalCurvature_pos hxL u v hplane

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_regions_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_regions_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_regions_properties ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.fixed_regions_properties

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }
private local instance quotientChartedSpace {B : ℝ} {hB : 0 < B} :
    ChartedSpace E3 (InsertionQuotient hB) := radialCapAttachmentChartedSpace transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientChartedSpace target :: scope.openDecls } }
private local instance quotientIsManifold {B : ℝ} {hB : 0 < B} :
    IsManifold (𝓡 3) ∞ (InsertionQuotient hB) := radialCapAttachment_isManifold transitionEnd_pos hB

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.quotientIsManifold target :: scope.openDecls } }

theorem normalizedDatum_positiveSideInsertionMetric_fixed_deep
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) {A : ℝ} (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    let hB := inv_pos.mpr d.precision_pos
    letI := radialCapAttachmentChartedSpace transitionEnd_pos hB
    letI := closedBallChartedSpace transitionEnd_pos
    ∀ (x : {x : E3 // ‖x‖ ≤ transitionEnd}), x.val ∈ deepRegion A →
      ∀ (v w : TangentSpace (𝓡∂ 3) x),
      (scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideInsertionMetric hA hAB)).inner
        (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB) x)
        (mfderiv (𝓡∂ 3) (𝓡 3) (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (adjunctionCell (radialCapBoundary transitionEnd_pos) (retainedBoundary hB)) x w) =
      (1 - Real.sqrt δ) * metric.inner x.val
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : {x : E3 // ‖x‖ ≤ transitionEnd} → E3) x v)
        (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : {x : E3 // ‖x‖ ≤ transitionEnd} → E3) x w) := by
  let := closedBallChartedSpace transitionEnd_pos
  dsimp only
  intro x hx v w
  have hx' : ‖x.val‖ < conformalRadius (-7 * A / 4) := hx.trans_lt (fixed_radii_bounds A).2.2.2
  have h := d.positiveSideInsertionMetric_cap_of_inner hA hAB x hx' v w
  rw [scaleMetric_inner, h]
  field_simp [d.scalar_pos.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.normalizedDatum_positiveSideInsertionMetric_fixed_deep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.normalizedDatum_positiveSideInsertionMetric_fixed_deep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.normalizedDatum_positiveSideInsertionMetric_fixed_deep ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.normalizedDatum_positiveSideInsertionMetric_fixed_deep
end DifferentialGeometry.PDE.RicciFlow.StandardCap
