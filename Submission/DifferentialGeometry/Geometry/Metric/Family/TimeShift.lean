import Submission.DifferentialGeometry.Geometry.Metric.Family.TimeComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem MetricFamilySmoothOn.timeShift
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (τ : ℝ) :
    MetricFamilySmoothOn (D.timeShift τ) (fun t => g (t + τ)) :=
  hg.comp_time (contDiff_id.add contDiff_const).contDiffOn
    (continuous_id.add continuous_const).continuousOn (fun _ hs => hs) (fun _ hs => hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.timeShift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.timeShift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.timeShift ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.timeShift

end DifferentialGeometry.Geometry.Curvature
