import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Curvature.ScalarPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Function _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold J N]

theorem metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (c : ℝ) (hc : 0 < c) (x : M) :
    metricScalarAt (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric c hc g) f hf hinj) x =
      metricScalarAt g (f x) / c := by
  rw [pullbackMetricOfInjectiveLocalDiffeomorph_scale_eq_chart g f hf hinj c hc
    hf.image (diffeomorphOntoImage f hf hinj) (diffeomorphOntoImage_apply f hf hinj)]
  rw [metricScalarAt_pullback_scaleMetric_restrictOpenCross, diffeomorphOntoImage_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale

end DifferentialGeometry.Geometry.Curvature
