import Submission.DifferentialGeometry.Geometry.Comparison.Nonnegative.BoundaryShiftTangent
import Submission.DifferentialGeometry.Geometry.Comparison.SliceParallelTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem shavingConcavity_of_sec_nonneg'
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) :
    ShavingConcavity (I := I) g :=
  shavingConcavity_of_sec_nonneg (I := I) g hEnorm hsec
    (fun _ hC hCclosed => hasSliceParallelTransport_of_totallyConvex (I := I) hEnorm hC hCclosed)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.shavingConcavity_of_sec_nonneg' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.shavingConcavity_of_sec_nonneg'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.shavingConcavity_of_sec_nonneg' ``Submission.DifferentialGeometry.Geometry.Topology.shavingConcavity_of_sec_nonneg'

theorem exists_soul_set_of_sec_nonneg' [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E :=
  exists_soul_set_of_sec_nonneg (I := I) g hEnorm hsec
    (fun _ hC hCclosed => hasSliceParallelTransport_of_totallyConvex (I := I) hEnorm hC hCclosed) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_soul_set_of_sec_nonneg' then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_soul_set_of_sec_nonneg'"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_soul_set_of_sec_nonneg' ``Submission.DifferentialGeometry.Geometry.Topology.exists_soul_set_of_sec_nonneg'

end DifferentialGeometry.Geometry.Topology

end
