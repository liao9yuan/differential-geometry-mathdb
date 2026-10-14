import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import Submission.DifferentialGeometry.Geometry.Metric.DerivativeENorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph
    (g h R : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f) (j : ℕ) (x : M) :
    metricDerivNorm j (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph R f hf hinj) x =
      metricDerivNorm j g h R (f x) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : SigmaCompactSpace hf.image := by
    apply isSigmaCompact_univ_iff.mp
    have hs := isSigmaCompact_range (diffeomorphOntoImage f hf hinj).contMDiff.continuous
    have heq : Set.range (fun x => diffeomorphOntoImage f hf hinj x) = Set.univ :=
      Set.range_eq_univ.mpr (diffeomorphOntoImage f hf hinj).surjective
    rw [heq] at hs
    exact hs
  unfold pullbackMetricOfInjectiveLocalDiffeomorph
  rw [metricDerivNorm_pullbackCross, metricDerivNorm_restrictOpen]
  rw [diffeomorphOntoImage_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph

theorem metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph
    (K : Set M) (k : ℕ) (g h R : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : _root_.Function.Injective f) :
    metricDerivENormSupOn K k (pullbackMetricOfInjectiveLocalDiffeomorph g f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph h f hf hinj)
      (pullbackMetricOfInjectiveLocalDiffeomorph R f hf hinj) =
      metricDerivENormSupOn (f '' K) k g h R := by
  simp only [metricDerivENormSupOn,
    metricDerivNorm_pullbackMetricOfInjectiveLocalDiffeomorph, iSup_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph ``Submission.DifferentialGeometry.Geometry.Metric.metricDerivENormSupOn_pullbackMetricOfInjectiveLocalDiffeomorph

end DifferentialGeometry.Geometry.Metric
