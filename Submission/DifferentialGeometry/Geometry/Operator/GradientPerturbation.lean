import Submission.DifferentialGeometry.Geometry.Operator.MetricComparison
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem abs_inner_gradFun_sub_le_of_metricDerivNorm
    (g h : SmoothRiemannianMetric I M) (F : M → ℝ) (x : M)
    (δ : ℝ) (hδ : δ < 1) (hmetric : metricDerivNorm 0 h g g x ≤ δ) :
    |h.inner x (gradFun h F x) (gradFun h F x) -
      g.inner x (gradFun g F x) (gradFun g F x)| ≤
      δ / (1 - δ) * g.inner x (gradFun g F x) (gradFun g F x) := by
  have hd : 0 < 1 - δ := by linarith
  have hb (v : TangentSpace I x) :
      |h.inner x v v - g.inner x v v| ≤ δ * g.inner x v v := by
    have hm := metricDifference_abs_le h g g x v v
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg g x v)] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right hmetric (metric_inner_self_nonneg g x v))
  let p := g.inner x (gradFun g F x) (gradFun g F x)
  let q := h.inner x (gradFun h F x) (gradFun h F x)
  have hp : 0 ≤ p := metric_inner_self_nonneg g x _
  have hq : 0 ≤ q := metric_inner_self_nonneg h x _
  have hu : q ≤ p / (1 - δ) := by
    have hh := inner_gradFun_le_of_metric_lower_bound g h F x (1 - δ)⁻¹ (by
      intro v
      rw [inv_mul_eq_div, le_div_iff₀ hd]
      have hh := (abs_le.mp (hb v)).1
      linarith)
    simpa only [inv_mul_eq_div] using hh
  have hl : p ≤ (1 + δ) * q :=
    inner_gradFun_le_of_metric_lower_bound h g F x (1 + δ) (by
      intro v
      have hh := (abs_le.mp (hb v)).2
      linarith)
  have hl' : (1 - δ) * p ≤ q := by
    have hh := mul_le_mul_of_nonneg_left hl hd.le
    nlinarith [mul_nonneg (sq_nonneg δ) hq]
  have hc : δ * p ≤ δ / (1 - δ) * p := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith [mul_nonneg (sq_nonneg δ) hp]
  change |q - p| ≤ δ / (1 - δ) * p
  rw [abs_le]
  constructor
  · linarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    rw [le_div_iff₀ hd] at hu
    nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.abs_inner_gradFun_sub_le_of_metricDerivNorm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.abs_inner_gradFun_sub_le_of_metricDerivNorm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.abs_inner_gradFun_sub_le_of_metricDerivNorm ``Submission.DifferentialGeometry.Geometry.Operator.abs_inner_gradFun_sub_le_of_metricDerivNorm

end DifferentialGeometry.Geometry.Operator
