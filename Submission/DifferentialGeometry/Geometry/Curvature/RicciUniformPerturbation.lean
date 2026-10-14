import Submission.DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import Submission.DifferentialGeometry.Geometry.Curvature.RicciTraceEstimate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Geometry.Curvature

theorem abs_ricci_difference_bound_of_small_metric_derivatives
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g gRef : SmoothRiemannianMetric I M) (x : M) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g gRef gRef x ≤ ε)
    (v w : TangentSpace I x) :
    |ricciTensor g x v w - ricciTensor gRef x v w| ≤
      240 * (Module.finrank ℝ E : ℝ) * ε *
        Real.sqrt (gRef.inner x v v) * Real.sqrt (gRef.inner x w w) := by
  have h := abs_ricci_difference_le_of_riemann_difference g gRef gRef x (240 * ε)
    (riemann_difference_bound_of_small_metric_derivatives g gRef x ε hε hsmall) v w
  convert h using 1
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.abs_ricci_difference_bound_of_small_metric_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.abs_ricci_difference_bound_of_small_metric_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.abs_ricci_difference_bound_of_small_metric_derivatives ``Submission.DifferentialGeometry.Geometry.Curvature.abs_ricci_difference_bound_of_small_metric_derivatives

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem ricciTensor_lower_bound_of_small_metric_derivatives
    (g G : SmoothRiemannianMetric I M) (x : M) {ε κ c : ℝ}
    (hε : ε ≤ 1 / 2) (hc : 0 ≤ c)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ ε)
    (hRic : ∀ v : TangentSpace I x, κ * G.inner x v v ≤ ricciTensor G x v v)
    (hbudget : c * (1 + ε) + 240 * (Module.finrank ℝ E : ℝ) * ε ≤ κ)
    (v : TangentSpace I x) : c * g.inner x v v ≤ ricciTensor g x v v := by
  have hdiff := abs_ricci_difference_bound_of_small_metric_derivatives g G x ε hε hsmall v v
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x v)] at hdiff
  have hmetric := (metricDifference_abs_le g G G x v v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hsmall 0 (by norm_num))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg G x v)] at hmetric
  have hm : g.inner x v v ≤ (1 + ε) * G.inner x v v := by
    linarith [(abs_le.mp hmetric).2]
  have hcm := mul_le_mul_of_nonneg_left hm hc
  have hb := mul_le_mul_of_nonneg_right hbudget (metric_inner_self_nonneg G x v)
  have hR := hRic v
  nlinarith [(abs_le.mp hdiff).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_lower_bound_of_small_metric_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_lower_bound_of_small_metric_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_lower_bound_of_small_metric_derivatives ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_lower_bound_of_small_metric_derivatives

end DifferentialGeometry.Geometry.Curvature
