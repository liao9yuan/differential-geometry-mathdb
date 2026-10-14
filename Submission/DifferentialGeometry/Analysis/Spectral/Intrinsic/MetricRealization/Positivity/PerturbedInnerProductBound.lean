import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Positivity.PositiveDefinitePerturbation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [Module.Finite ℝ E] in
theorem perturbedInner_self_upper_bound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) :
    perturbedInner g h x v v ≤ (1 + δ) * g.inner x v v := by
  have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hbound := hδ x v v
  have hsq : Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) = g.inner x v v := by
    rw [← Real.sqrt_mul hnn, Real.sqrt_mul_self hnn]
  have hdiag : |h x v v| ≤ δ * g.inner x v v := by
    calc |h x v v|
        ≤ δ * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v) := hbound
      _ = δ * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x v v)) := by ring
      _ = δ * g.inner x v v := by rw [hsq]
  have hle : h x v v ≤ δ * g.inner x v v := le_of_abs_le hdiag
  rw [perturbedInner_apply]
  nlinarith [hle]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_upper_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_upper_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_upper_bound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.perturbedInner_self_upper_bound

omit [Module.Finite ℝ E] in
theorem gInner_self_le_of_gFibreOpBound
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ : ℝ} (hδ : metricCauchySchwarzBound g h δ)
    (x : M) (v : TangentSpace I x) :
    g.inner x v v + h x v v ≤ (1 + δ) * g.inner x v v := by
  have h := perturbedInner_self_upper_bound (I := I) (M := M) g h hδ x v
  rwa [perturbedInner_apply] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.gInner_self_le_of_gFibreOpBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.gInner_self_le_of_gFibreOpBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.gInner_self_le_of_gFibreOpBound ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.gInner_self_le_of_gFibreOpBound

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
