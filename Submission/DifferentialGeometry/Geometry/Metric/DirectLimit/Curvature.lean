import Submission.DifferentialGeometry.Geometry.Metric.DirectLimit.Defs
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Set _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

namespace SmoothSeqSystem

variable {A : ℕ → Type*} [∀ j, TopologicalSpace (A j)] [∀ j, ChartedSpace H (A j)]
  [∀ j, IsManifold I ∞ (A j)] [∀ j, T2Space (A j)] [∀ j, Nonempty (A j)]

theorem metricScalarAt_limitMetric_incl
    (S : SmoothSeqSystem I A) (gInf : ∀ j, SmoothRiemannianMetric I (A j))
    (hg : S.MetricCocycle gInf) (j : ℕ) (a : A j) :
    metricScalarAt (I := I) (S.limitMetric gInf hg) (S.toSeqSystem.incl j a) =
      metricScalarAt (I := I) (gInf j) a := by
  have hloc : IsLocalDiffeomorph I I ∞ (S.toSeqSystem.incl j) := fun a =>
    (S.inclPartialDiffeo j).symm.isLocalDiffeomorphAt I I ∞ (show a ∈ Set.univ from _root_.Set.mem_univ a)
  have heq : gInf j = localPullMetric (S.limitMetric gInf hg) (S.toSeqSystem.incl j) hloc := by
    apply SmoothRiemannianMetric.ext_inner
    intro a v w
    rw [localPullMetric_inner, S.limitMetric_pullback]
  rw [heq, metricScalarAt_localPull]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.SmoothSeqSystem.metricScalarAt_limitMetric_incl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.SmoothSeqSystem.metricScalarAt_limitMetric_incl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.SmoothSeqSystem.metricScalarAt_limitMetric_incl ``Submission.DifferentialGeometry.SmoothSeqSystem.metricScalarAt_limitMetric_incl

end SmoothSeqSystem

end DifferentialGeometry
