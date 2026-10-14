import Submission.DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian (SectionalBoundedBelowAt
  ricci_lower_of_sectionalBoundedBelowAt)
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt
    (g : SmoothRiemannianMetric I M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ) :
    SectionalBoundedBelowAt g x (-δ) := by
  intro v w
  have hq := h 1 (fun _ => 1) (fun _ => v) (fun _ => w)
  simp only [algebraicCurvatureOperatorQuadraticEval, algebraicCurvatureIdentityQuadraticEval,
    Fin.sum_univ_one, one_mul, metricAlgebraicCurvatureTensorAt_coe] at hq
  change 0 ≤ metricRm04StandardAt g x v w w v + _ at hq
  rw [g.symm x w v] at hq
  nlinarith [hq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt ``Submission.DifferentialGeometry.Geometry.Curvature.sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt

theorem neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M) {δ : ℝ}
    (h : curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) δ)
    (u : TangentSpace I x) :
    -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * δ) * g.inner x u u ≤ metricRicciAt g x (vec2 u u) := by
  rw [metricRicciAt_apply_eq_ricciTensor]
  have hric := ricci_lower_of_sectionalBoundedBelowAt g x
    (sectionalBoundedBelowAt_of_curvatureOperatorLowerBoundAt g x h) u
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt ``Submission.DifferentialGeometry.Geometry.Curvature.neg_mul_inner_le_metricRicciAt_of_curvatureOperatorLowerBoundAt

end DifferentialGeometry.Geometry.Curvature

end
