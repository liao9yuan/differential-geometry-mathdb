import Mathlib.Geometry.Manifold.Instances.Real
import Submission.DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Function _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Metric
private abbrev CompE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Metric.CompE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Metric.CompE3 target :: scope.openDecls } }
variable {S T : Type*} [TopologicalSpace S] [ChartedSpace CompE3 S] [IsManifold (𝓡 3) ∞ S]
  [TopologicalSpace T] [ChartedSpace CompE3 T] [IsManifold (𝓡 3) ∞ T]
variable {E H P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace P] [ChartedSpace H P]

theorem metric_inner_comp_of_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) = g.inner x v w)
    (φ : P → S) (hφ : ContMDiff I (𝓡 3) ∞ φ) (x : P) (v w : TangentSpace I x) :
    h.inner ((f ∘ φ) x) (mfderiv I (𝓡 3) (f ∘ φ) x v) (mfderiv I (𝓡 3) (f ∘ φ) x w) =
      g.inner (φ x) (mfderiv I (𝓡 3) φ x v) (mfderiv I (𝓡 3) φ x w) := by
  rw [mfderiv_comp x (hf.mdifferentiable (by simp) (φ x)) (hφ.mdifferentiable (by simp) x)]
  exact hmetric (φ x) (mfderiv I (𝓡 3) φ x v) (mfderiv I (𝓡 3) φ x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.metric_inner_comp_of_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.metric_inner_comp_of_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.metric_inner_comp_of_isometry ``Submission.DifferentialGeometry.Geometry.Metric.metric_inner_comp_of_isometry

variable [T2Space S] [T2Space T]
variable {V : Type*} [TopologicalSpace V] [ChartedSpace CompE3 V] [IsManifold (𝓡 3) ∞ V] [T2Space V]

theorem scaled_pullback_comp_of_isometry
    (g : SmoothRiemannianMetric (𝓡 3) S) (h : SmoothRiemannianMetric (𝓡 3) T)
    (f : S → T) (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) (hinj : _root_.Function.Injective f)
    (hmetric : ∀ (x : S) (v w : TangentSpace (𝓡 3) x),
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) = g.inner x v w)
    (φ : V → S) (hφ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ φ) (hφinj : _root_.Function.Injective φ)
    (c : ℝ) (hc : 0 < c) :
    pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric c hc h) (f ∘ φ)
      (fun q => (hφ q).comp (𝓡 3) T (hf (φ q))) (hinj.comp hφinj) =
        pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric c hc g) φ hφ hφinj := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  have hl := pullbackMetricOfInjectiveLocalDiffeomorph_inner (scaleMetric c hc h) (f ∘ φ)
    (fun q => (hφ q).comp (𝓡 3) T (hf (φ q))) (hinj.comp hφinj) q v w
  have hr := pullbackMetricOfInjectiveLocalDiffeomorph_inner (scaleMetric c hc g) φ hφ hφinj q v w
  rw [scaleMetric_inner] at hl hr
  exact hl.trans ((congrArg (fun t => c * t)
    (metric_inner_comp_of_isometry g h f hf.contMDiff hmetric φ hφ.contMDiff q v w)).trans hr.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.scaled_pullback_comp_of_isometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.scaled_pullback_comp_of_isometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.scaled_pullback_comp_of_isometry ``Submission.DifferentialGeometry.Geometry.Metric.scaled_pullback_comp_of_isometry
end DifferentialGeometry.Geometry.Metric
