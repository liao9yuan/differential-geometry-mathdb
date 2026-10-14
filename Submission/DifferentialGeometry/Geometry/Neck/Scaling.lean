import Submission.DifferentialGeometry.Geometry.Neck.InsertionInput
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.IC target :: scope.openDecls } }
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

private theorem rescaled_scalar_pos (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    0 < metricScalarAt (scaleMetric c hc g) x₀ := by
  rw [metricScalarAt_scaleMetric]
  exact mul_pos (inv_pos.mpr hc) d.scalar_pos

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_scalar_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_scalar_pos target :: scope.openDecls } }

private theorem rescaled_center_metric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (rescaled_scalar_pos d c hc)
        (scaleMetric c hc g) = scaleMetric (metricScalarAt g x₀) d.scalar_pos g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x u v
  rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner, metricScalarAt_scaleMetric]
  field_simp [hc.ne']

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_center_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_center_metric target :: scope.openDecls } }

def rescaled (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    normalizedDatum (scaleMetric c hc g) x₀ δ k := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E := by
    rw [show Module.finrank ℝ E = 3 from Fact.out]
    simp
  let hloc := isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion hdim
  refine
    { precision_pos := d.precision_pos
      precision_lt_one := d.precision_lt_one
      map := d.map
      smooth := d.smooth
      injective := d.injective
      immersion := d.immersion
      center_eq := d.center_eq
      scalar_pos := rescaled_scalar_pos d c hc
      retainedSide := d.retainedSide
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt (scaleMetric c hc g) x₀) (rescaled_scalar_pos d c hc)
        (scaleMetric c hc g)) d.map hloc d.injective)
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
  rw [rescaled_center_metric d c hc]
  exact d.error_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled

theorem rescaled_map (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).map = d.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_map ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_map

theorem rescaled_retainedSide (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).retainedSide = d.retainedSide := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_retainedSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_retainedSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_retainedSide ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_retainedSide

theorem rescaled_normalizedMetric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).normalizedMetric = d.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x u v
  rw [normalizedMetric_inner, normalizedMetric_inner, rescaled_map,
    scaleMetric_inner, metricScalarAt_scaleMetric]
  field_simp [hc.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_normalizedMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_normalizedMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_normalizedMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_normalizedMetric

theorem rescaled_controlledMetric (d : normalizedDatum g x₀ δ k) (c : ℝ) (hc : 0 < c) :
    (d.rescaled c hc).controlledMetric = d.controlledMetric := by
  change (d.rescaled c hc).normalizedMetric.restrictOpenOfSubset _ = d.normalizedMetric.restrictOpenOfSubset _
  rw [rescaled_normalizedMetric]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_controlledMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_controlledMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_controlledMetric ``Submission.DifferentialGeometry.Geometry.Neck.normalizedDatum.rescaled_controlledMetric

end DifferentialGeometry.Geometry.Neck.normalizedDatum
