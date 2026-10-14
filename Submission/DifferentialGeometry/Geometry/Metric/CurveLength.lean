import Submission.DifferentialGeometry.Geometry.Metric.LipschitzCurveIntegration

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



def riemannianCurveLength (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : ℝ := (riemannianCurveELength g γ a b).toReal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength

theorem riemannianCurveLength_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : ℝ → M) (a b : ℝ) : 0 ≤ riemannianCurveLength g γ a b := ENNReal.toReal_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength_nonneg ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength_nonneg



theorem riemannianCurveLength_eq_integral [FiniteDimensional ℝ E] [CompactSpace M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {C : ℝ≥0}
    (hγ : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (C : ℝ≥0∞) * _root_.EDist.edist x y) (a b : ℝ) :
    riemannianCurveLength g γ a b = ∫ t in _root_.Set.Icc a b, riemannianCurveSpeed g γ t := by
  exact (_root_.MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (riemannianCurveSpeed_nonneg g γ))
    (aestronglyMeasurable_riemannianCurveSpeed g hγ).restrict).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianCurveLength_eq_integral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianCurveLength_eq_integral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianCurveLength_eq_integral ``Submission.DifferentialGeometry.Geometry.riemannianCurveLength_eq_integral

end DifferentialGeometry.Geometry
