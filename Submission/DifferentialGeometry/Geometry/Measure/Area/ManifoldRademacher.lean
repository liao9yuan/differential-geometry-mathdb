import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldRademacherSource

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission












noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

theorem exists_open_ae_mdifferentiableAt_of_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y)
    (z : ℂ) : ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
      ∀ᵐ w ∂volume, w ∈ U → MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u w :=
  exists_open_ae_mdifferentiableAt_of_metric_lipschitz g hu z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_lipschitz ``Submission.DifferentialGeometry.Geometry.exists_open_ae_mdifferentiableAt_of_lipschitz



theorem ae_mdifferentiableAt_of_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : ℂ → M} {C : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) :
    ∀ᵐ z ∂volume, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z :=
  ae_mdifferentiableAt_of_metric_lipschitz g hu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_riemannian_lipschitz ``Submission.DifferentialGeometry.Geometry.ae_mdifferentiableAt_of_riemannian_lipschitz

end DifferentialGeometry.Geometry
