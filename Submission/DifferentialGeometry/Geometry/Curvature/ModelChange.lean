import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Metric.ModelChange

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Geometry.Curvature

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem metricScalarAt_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I M) (e : E ≃L[ℝ] F) (x : M) :
    metricScalarAt (g.transContinuousLinearEquiv e) x = metricScalarAt g x := by
  change metricScalarAt (Diffeomorph.pullbackMetricCross g
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm) x = _
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric]
  exact metricScalarAt_localPull g
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I M e).symm.isLocalDiffeomorph x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricScalarAt_transContinuousLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricScalarAt_transContinuousLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricScalarAt_transContinuousLinearEquiv ``Submission.DifferentialGeometry.Geometry.Curvature.metricScalarAt_transContinuousLinearEquiv

end

end DifferentialGeometry.Geometry.Curvature
