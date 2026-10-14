import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.TensorError

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

noncomputable def MapMetricApproximationOn.ofMetricDerivNorm
    {K : Set M} {eps : ℝ} {p : ℕ} {F : M → N}
    (G g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (happly : ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) G x v =
        h.inner (F x)
          (mfderiv I I F x (v 0)) (mfderiv I I F x (v 1)))
    (hderiv : ∀ a : ℕ, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a G g g x ≤ eps) :
    MapMetricApproximationOn (I := I) K eps p F g h where
  eps_pos := heps
  eps_lt_one := heps1
  smoothOn := hsmooth
  pullback := Tensor0SBundle.metricTensorField (I := I) G
  pullback_apply := happly
  c0_small := by
    intro x hx
    rw [metricTensorErrorNorm_eq_metricDerivNorm_zero (I := I) G g x]
    exact hderiv 0 (Nat.zero_le p) x hx
  cov_deriv_small := by
    intro a ha hap x hx
    rw [tensor02CovDerivNormWith_metricTensorField_eq_metricDerivNorm
      (I := I) G g a ha x]
    exact hderiv a hap x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.ofMetricDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.ofMetricDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.ofMetricDerivNorm ``Submission.DifferentialGeometry.CheegerGromovCompactness.MapMetricApproximationOn.ofMetricDerivNorm

end CheegerGromovCompactness
end DifferentialGeometry
