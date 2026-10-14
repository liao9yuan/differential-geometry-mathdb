import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import Submission.DifferentialGeometry.Geometry.Measure.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Manifold _root_.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Measure.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem riemannianVolumeMeasure_ball_le_of_inner_bounds
    (g h : SmoothRiemannianMetric I M) {C D : ℝ} (hC : 0 < C) (hD : 0 < D)
    (p : M) (r : ℝ)
    (hlower : ∀ x ∈ riemannianBallOf g p r, ∀ v : TangentSpace I x,
      g.inner x v v ≤ C * h.inner x v v)
    (hupper : ∀ x : M, ∀ v : TangentSpace I x,
      h.inner x v v ≤ D * g.inner x v v) :
    riemannianVolumeMeasure I M g (riemannianBallOf g p r) ≤
      ENNReal.ofReal (Real.sqrt (C ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure I M h (riemannianBallOf h p (Real.sqrt D * r)) := by
  have hmeas : MeasurableSet (riemannianBallOf g p r) :=
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist g p)
      continuous_const).measurableSet
  have hsub : riemannianBallOf g p r ⊆ riemannianBallOf h p (Real.sqrt D * r) := by
    intro x hx
    change riemannianEDistOf h p x < ENNReal.ofReal (Real.sqrt D * r)
    have hdist := edistOf_le_of_quad g h hD hupper p x
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg D)]
    exact hdist.trans_lt ((ENNReal.mul_lt_mul_iff_right
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hD)))
      ENNReal.ofReal_ne_top).mpr hx)
  exact (riemannianVolumeMeasure_apply_le_of_inner_le h g hC hmeas hlower).trans
    (mul_le_mul' le_rfl (_root_.MeasureTheory.measure_mono hsub))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_inner_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_inner_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_inner_bounds ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_le_of_inner_bounds

section

theorem riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) (κ : ℝ≥0∞) :
    κ * ENNReal.ofReal (Real.sqrt c * r) ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I M (scaleMetric c hc g)
        (riemannianBallOf (scaleMetric c hc g) p (Real.sqrt c * r)) ↔
    κ * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g p r) := by
  rw [riemannianBallOf_scaleMetric, volume_scale_apply,
    ENNReal.ofReal_mul (Real.sqrt_nonneg c), mul_pow]
  rw [← mul_assoc, mul_comm κ, mul_assoc]
  exact ENNReal.mul_le_mul_iff_right
    (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc))))
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff ``Submission.DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff

end

end DifferentialGeometry.Geometry.Measure
