import Submission.DifferentialGeometry.Geometry.Comparison.Variation.EndpointGerms

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem centralVariationAcceleration_eq_of_endpoint_germ
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (b : ℝ)
    {beta : ℝ → M} (heq : (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta) :
    (centralVariationAcceleration g f b : E) =
      (covDerivAlong g beta (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) 0 : E) := by
  have hvel : ∀ᶠ u in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r b) u (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ) : E) := by
    filter_upwards [heq.eventually_nhds] with u hu
    have hueq : (fun r ↦ f r b) =ᶠ[𝓝 u] beta := hu
    exact congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) (u : ℝ) →L[ℝ] TangentSpace I (f u b) ↦ L (1 : ℝ))
      (hueq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
  exact covDerivAlong_congr_curve g
    (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ f r b) u (1 : ℝ))
    (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I beta u (1 : ℝ)) heq hvel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration_eq_of_endpoint_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration_eq_of_endpoint_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration_eq_of_endpoint_germ ``Submission.DifferentialGeometry.Geometry.Riemannian.Variation.centralVariationAcceleration_eq_of_endpoint_germ

end DifferentialGeometry.Geometry.Riemannian.Variation
