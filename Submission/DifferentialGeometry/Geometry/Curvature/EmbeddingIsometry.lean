import Submission.DifferentialGeometry.Geometry.Curvature.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Curvature.OperatorNaturality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric
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

theorem curvature_of_injective_local_isometry
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) (x : M) :
    metricScalarAt g x = metricScalarAt h (f x) ∧
      leastCurvatureOperatorEigenvalueAt g x (metricAlgebraicCurvatureTensorAt g x) =
        leastCurvatureOperatorEigenvalueAt h (f x) (metricAlgebraicCurvatureTensorAt h (f x)) := by
  have he : g = pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hmetric q v w
  have hone : scaleMetric 1 zero_lt_one h = h := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [scaleMetric_inner, one_mul]
  constructor
  · have hr := metricScalarAt_pullbackMetricOfInjectiveLocalDiffeomorph_scale h f hf hinj 1 zero_lt_one x
    simpa only [hone, div_one, ← he] using hr
  · rw [he]
    exact leastCurvatureOperatorEigenvalueAt_pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvature_of_injective_local_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvature_of_injective_local_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvature_of_injective_local_isometry ``Submission.DifferentialGeometry.Geometry.Curvature.curvature_of_injective_local_isometry
end DifferentialGeometry.Geometry.Curvature
