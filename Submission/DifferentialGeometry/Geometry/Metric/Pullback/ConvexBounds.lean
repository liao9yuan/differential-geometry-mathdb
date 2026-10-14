import Submission.DifferentialGeometry.Geometry.Metric.CompactSourceEllipticity
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.Calculus.ContDiff.RCLike

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

set_option autoImplicit false
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_pullback_metric_bounds_on_convex_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞) (L : F ≃L[ℝ] E)
    {K : Set F} (hK : IsCompact K) (hKconv : Convex ℝ K) (hKsource : _root_.Set.MapsTo L K Φ.source) :
    let ψ := fun y => Φ (L y)
    let B := pullbackMetricCoefficients g ψ
    ∃ lam : ℝ, ∃ C : ℝ≥0, 0 < lam ∧
      (∀ y ∈ K, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ B y ξ ξ) ∧ LipschitzOnWith C B K := by
  let ψ := fun y => Φ (L y)
  let U := L ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage L.continuous
  have hψ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ U :=
    Φ.contMDiffOn_toFun.comp L.contDiff.contMDiff.contMDiffOn (fun _ hy => hy)
  have hinj (y : F) (hy : y ∈ K) : Function.Injective (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) ψ y) := by
    have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ ψ y :=
      (L.toDiffeomorph.isLocalDiffeomorph y).comp 𝓘(ℝ, E) M
        (Φ.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (hKsource hy))
    exact (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  obtain ⟨lam, _, hlam, _, hbound⟩ := exists_compact_source_metric_ellipticity g hU
    (hψ.of_le (by simp)) hK hKsource hinj
  have hB := (contDiffOn_pullback_metric_coefficients g hU hψ).mono hKsource
  obtain ⟨C, hC⟩ := hB.exists_lipschitzOnWith (by simp) hKconv hK
  exact ⟨lam, C, hlam, fun y hy ξ => (hbound y hy ξ).1, hC⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_pullback_metric_bounds_on_convex_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_pullback_metric_bounds_on_convex_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_pullback_metric_bounds_on_convex_chart ``Submission.DifferentialGeometry.Geometry.exists_pullback_metric_bounds_on_convex_chart

end DifferentialGeometry.Geometry

end

end
