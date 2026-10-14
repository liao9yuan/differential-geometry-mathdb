import Submission.DifferentialGeometry.Geometry.Metric.CurveVariation
import Submission.DifferentialGeometry.Analysis.Calculus.Variation.Periodic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.Function
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace



theorem riemannianCurveLength_unit_period (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (hp : _root_.Function.Periodic γ 1) (a : ℝ) :
    riemannianCurveLength g γ a (a + 1) = riemannianCurveLength g γ 0 1 := by
  rw [riemannianCurveLength_eq_variation g hγ, riemannianCurveLength_eq_variation g hγ]
  apply congrArg ENNReal.toReal
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact DifferentialGeometry.Analysis.eVariationOn_unit_period hp a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength_unit_period then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength_unit_period"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength_unit_period ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength_unit_period




theorem riemannianCurveLength_comp_monotone_lift (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} {C D : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (hp : _root_.Function.Periodic γ 1) {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hm : Monotone ψ)
    (hdegree : ∀ t, ψ (t + 1) = ψ t + 1)
    (hcomp : ∀ x y, riemannianEDistOf g (γ (ψ x)) (γ (ψ y)) ≤ (D : ℝ≥0∞) * _root_.EDist.edist x y) :
    riemannianCurveLength g (γ ∘ ψ) 0 1 = riemannianCurveLength g γ 0 1 := by
  rw [riemannianCurveLength_eq_variation g (γ := γ ∘ ψ) hcomp, riemannianCurveLength_eq_variation g hγ]
  apply congrArg ENNReal.toReal
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact DifferentialGeometry.Analysis.eVariationOn_comp_monotone_lift hp hψ hm hdegree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength_comp_monotone_lift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength_comp_monotone_lift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength_comp_monotone_lift ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength_comp_monotone_lift

end DifferentialGeometry.Geometry
