import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {JH : Type*} [TopologicalSpace JH] {J : ModelWithCorners ℝ F JH}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace JH N] [IsManifold J ∞ N] [T2Space N]

theorem curvatureOperatorLowerBoundAt_localPullMetric_iff
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) (K : ℝ) :
    curvatureOperatorLowerBoundAt (localPullMetric g f hf) x
      (metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x) K ↔
    curvatureOperatorLowerBoundAt g (f x) (metricAlgebraicCurvatureTensorAt g (f x)) K := by
  have he (n : ℕ) (c : Fin n → ℝ) (v w : Fin n → TangentSpace I x) :
      algebraicCurvatureOperatorQuadraticEval
          (metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x) c v w +
        K * algebraicCurvatureIdentityQuadraticEval (localPullMetric g f hf) c v w =
      algebraicCurvatureOperatorQuadraticEval (metricAlgebraicCurvatureTensorAt g (f x)) c
          (fun i => mfderiv I J f x (v i)) (fun i => mfderiv I J f x (w i)) +
        K * algebraicCurvatureIdentityQuadraticEval g c
          (fun i => mfderiv I J f x (v i)) (fun i => mfderiv I J f x (w i)) := by
    simp only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt_coe,
      show ∀ h : SmoothRiemannianMetric I M, ∀ a b c d : TangentSpace I x,
        tensor04StandardAt (metricRm04At h x) a b c d = metricRm04StandardAt h x a b c d from
        fun _ _ _ _ _ => rfl,
      metricRm04StandardAt_localPullMetric, algebraicCurvatureIdentityQuadraticEval,
      localPullMetric_inner]
    rfl
  constructor
  · intro h n c v w
    have hs : Function.Surjective (mfderiv I J f x) := by
      exact (hf.mfderivToContinuousLinearEquiv (x := x) (by simp)).surjective
    choose v' hv using fun i => hs (v i)
    choose w' hw using fun i => hs (w i)
    have hh := h n c v' w'
    rw [he] at hh
    simpa only [hv, hw] using hh
  · intro h n c v w
    rw [he]
    exact h n c _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_localPullMetric_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_localPullMetric_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_localPullMetric_iff ``Submission.DifferentialGeometry.Geometry.Curvature.curvatureOperatorLowerBoundAt_localPullMetric_iff

theorem metricAlgebraicCurvatureTensorAt_localPullMetric_mem_nonnegativeCone_iff
    (g : SmoothRiemannianMetric J N) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (x : M) :
    metricAlgebraicCurvatureTensorAt (localPullMetric g f hf) x ∈
        algebraicCurvatureOperatorNonnegativeCone ↔
      metricAlgebraicCurvatureTensorAt g (f x) ∈
        algebraicCurvatureOperatorNonnegativeCone := by
  simpa only [mem_algebraicCurvatureOperatorNonnegativeCone,
    curvatureOperatorLowerBoundAt, _root_.MulZeroClass.zero_mul, add_zero] using
    curvatureOperatorLowerBoundAt_localPullMetric_iff g f hf x 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_localPullMetric_mem_nonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_localPullMetric_mem_nonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_localPullMetric_mem_nonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_localPullMetric_mem_nonnegativeCone_iff

theorem metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    metricAlgebraicCurvatureTensorAt (Diffeomorph.pullbackMetricCross g Φ) x ∈
        algebraicCurvatureOperatorNonnegativeCone ↔
      metricAlgebraicCurvatureTensorAt g (Φ x) ∈
        algebraicCurvatureOperatorNonnegativeCone := by
  rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    metricAlgebraicCurvatureTensorAt_localPullMetric_mem_nonnegativeCone_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff ``Submission.DifferentialGeometry.Geometry.Curvature.metricAlgebraicCurvatureTensorAt_pullbackMetricCross_mem_nonnegativeCone_iff

end DifferentialGeometry.Geometry.Curvature
