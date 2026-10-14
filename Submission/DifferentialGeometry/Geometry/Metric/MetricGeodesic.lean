import Submission.DifferentialGeometry.Geometry.Metric.ShortGeodesicBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission








noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace


def metricShortGeodesic (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : M → M → ℝ → M :=
  letI : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
  shortGeodesic g hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.metricShortGeodesic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.metricShortGeodesic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.metricShortGeodesic ``Submission.DifferentialGeometry.Geometry.metricShortGeodesic



theorem metricShortGeodesic_spec (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    (∀ x y, metricShortGeodesic g x y 0 = x) ∧
    (∀ x y, riemannianEDistOf g x y ≠ ⊤ → metricShortGeodesic g x y 1 = y) ∧
    (∀ x t, metricShortGeodesic g x x t = x) ∧
    (∀ x y, riemannianEDistOf g x y ≠ ⊤ → ∀ t,
      Real.sqrt (g.inner (metricShortGeodesic g x y t)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (metricShortGeodesic g x y) t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (metricShortGeodesic g x y) t 1)) =
          (riemannianEDistOf g x y).toReal) ∧
    ∃ (ρ : ℝ≥0) (W : Set (ℝ × (M × M))), 0 < ρ ∧ IsOpen W ∧
      (∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ∀ x y,
        riemannianEDistOf g x y ≤ (ρ : ℝ≥0∞) → (t, (x, y)) ∈ W) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓘(ℝ, E).prod 𝓘(ℝ, E))) 𝓘(ℝ, E) ∞
        (fun p : ℝ × (M × M) => metricShortGeodesic g p.2.1 p.2.2 p.1) W := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let hg : IsMetricNorm (I := 𝓘(ℝ, E)) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓘(ℝ, E)) g x v
  exact ⟨shortGeodesic_zero g hg, fun _ _ h => shortGeodesic_one g hg h,
    shortGeodesic_self g hg, fun _ _ h t => shortGeodesic_speed g hg h t,
    exists_uniform_smooth_shortGeodesic g hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.metricShortGeodesic_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.metricShortGeodesic_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.metricShortGeodesic_spec ``Submission.DifferentialGeometry.Geometry.metricShortGeodesic_spec

end DifferentialGeometry.Geometry
