import Submission.DifferentialGeometry.Geometry.Curvature.PositiveSectional
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import Submission.DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import Submission.DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Geometry.Metric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCover_liftedMetric_eq_localPull (g : SmoothRiemannianMetric I M) :
    UniversalCover.liftedMetric g = localPullMetric g UniversalCover.proj
      (UniversalCover.proj_localDiffeo (I := I)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, (UniversalCover.hasMFDerivAt_proj (I := I) x).mfderiv]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.universalCover_liftedMetric_eq_localPull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.universalCover_liftedMetric_eq_localPull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.universalCover_liftedMetric_eq_localPull ``Submission.DifferentialGeometry.Geometry.universalCover_liftedMetric_eq_localPull

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem HasPositiveSectionalCurvature.universalCoverMetric
    {g : SmoothRiemannianMetric I M} (hg : HasPositiveSectionalCurvature g) :
    HasPositiveSectionalCurvature (UniversalCover.liftedMetric (I := I) g) := by
  intro x v w hvw
  exact lt_of_lt_of_eq (hg (UniversalCover.proj x) v w hvw)
    (UniversalCover.metricRm_lifted (I := I) g x v w w v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.universalCoverMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.universalCoverMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.universalCoverMetric ``Submission.DifferentialGeometry.Geometry.HasPositiveSectionalCurvature.universalCoverMetric

omit [SigmaCompactSpace M] [ConnectedSpace M] in
theorem universalCover_orthonormal_sectional_bound (g : SmoothRiemannianMetric I M) {k : ℝ}
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v v = 1 → g.inner x w w = 1 → g.inner x v w = 0 →
        k ≤ metricRm04StandardAt g x v w w v) :
    ∀ (x : UniversalCover M) (v w : TangentSpace I x),
      (UniversalCover.liftedMetric g).inner x v v = 1 →
      (UniversalCover.liftedMetric g).inner x w w = 1 →
      (UniversalCover.liftedMetric g).inner x v w = 0 →
        k ≤ metricRm04StandardAt (UniversalCover.liftedMetric g) x v w w v := by
  intro x v w hv hw hvw
  exact le_trans (hsec (UniversalCover.proj x) v w hv hw hvw)
    (UniversalCover.metricRm_lifted (I := I) g x v w w v).symm.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.universalCover_orthonormal_sectional_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.universalCover_orthonormal_sectional_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.universalCover_orthonormal_sectional_bound ``Submission.DifferentialGeometry.Geometry.universalCover_orthonormal_sectional_bound

end DifferentialGeometry.Geometry
