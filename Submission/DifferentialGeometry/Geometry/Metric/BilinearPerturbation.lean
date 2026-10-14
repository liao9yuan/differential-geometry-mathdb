import Submission.DifferentialGeometry.Geometry.Metric.DerivativeENorm
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal
namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem inner_bounds_of_metricDerivNorm_le
    (g h : SmoothRiemannianMetric I M) (x : M) {δ : ℝ}
    (herr : metricDerivNorm 0 h g g x ≤ δ) (v : TangentSpace I x) :
    (1 - δ) * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ (1 + δ) * g.inner x v v := by
  have hb := metricDifference_abs_le h g g x v v
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg g x v)] at hb
  have he := hb.trans (mul_le_mul_of_nonneg_right herr (metric_inner_self_nonneg g x v))
  obtain ⟨hl, hu⟩ := abs_le.mp he
  constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le ``Submission.DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivNorm_le

theorem inner_bounds_of_metricDerivENormSupOn_lt
    (g h : SmoothRiemannianMetric I M) {K : Set M} {k : ℕ} {δ : ℝ}
    (herr : metricDerivENormSupOn K k h g g < ENNReal.ofReal δ)
    {x : M} (hx : x ∈ K) (v : TangentSpace I x) :
    (1 - δ) * g.inner x v v ≤ h.inner x v v ∧
      h.inner x v v ≤ (1 + δ) * g.inner x v v :=
  inner_bounds_of_metricDerivNorm_le g h x
    (metricDerivNorm_lt_of_sup_lt K k h g g herr (Nat.zero_le k) hx).le v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivENormSupOn_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivENormSupOn_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivENormSupOn_lt ``Submission.DifferentialGeometry.Geometry.Metric.inner_bounds_of_metricDerivENormSupOn_lt

end DifferentialGeometry.Geometry.Metric
