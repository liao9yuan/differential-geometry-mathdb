import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PinchingDatum
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.CurvatureOperator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E F H JH M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace JH]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F JH}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace JH N] [IsManifold J ∞ N] [T2Space N]
  {D : Geometry.Curvature.RealTimeInterval}

theorem PhiAlmostNonnegative.localPullback
    {S : SolutionOn (I := J) (M := N) D} {W : Set ℝ} {Phi : ℝ → ℝ}
    (hS : PhiAlmostNonnegative S W Phi)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) :
    PhiAlmostNonnegative (S.localPullback f hf) W Phi := by
  intro t ht x
  change curvatureOperatorLowerBoundAt
    (localPullMetric (S.base.metric t) f hf) x
    (metricAlgebraicCurvatureTensorAt (localPullMetric (S.base.metric t) f hf) x)
    (Phi (metricScalarAt (localPullMetric (S.base.metric t) f hf) x))
  rw [metricScalarAt_localPull, curvatureOperatorLowerBoundAt_localPullMetric_iff]
  exact hS t ht (f x)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative.localPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative.localPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative.localPullback ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.PhiAlmostNonnegative.localPullback

end DifferentialGeometry.PDE.RicciFlow.Perelman
