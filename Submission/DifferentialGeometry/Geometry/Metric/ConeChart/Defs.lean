import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Riemannian

universe u uE uH v
section Chart
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

structure ConeChart (m : ℕ) (g : SmoothRiemannianMetric I M) (U : Set M) where
  surface : Type v
  [topology : TopologicalSpace surface]
  [charted : ChartedSpace (EuclideanSpace ℝ (Fin m)) surface]
  [smooth : IsManifold (𝓡 m) ∞ surface]
  [t2 : T2Space surface]
  [sigmaCompact : SigmaCompactSpace surface]
  metric : SmoothRiemannianMetric (𝓡 m) surface
  map : PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 m)) I (ℝ × surface) M ∞
  positive_radius : ∀ z ∈ map.source, 0 < z.1
  target_eq : map.target = U
  radial_metric : ∀ z ∈ map.source, ∀ v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 m)) z,
    g.inner (map z) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I map z v)
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I map z w) =
        v.1 * w.1 + z.1 ^ 2 * metric.inner z.2 v.2 w.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.ConeChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.ConeChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.ConeChart ``Submission.DifferentialGeometry.Geometry.Riemannian.ConeChart
end Chart

end DifferentialGeometry.Geometry.Riemannian
