import Submission.DifferentialGeometry.Geometry.Connection.SourceSectionPairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open _root_.Filter
open scoped _root_.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem sourceSectionCovariantDerivative_parameter_slice
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (F : ℝ × A → M)
    (W : ∀ p, TangentSpace 𝓘(ℝ, E) (F p)) (t : ℝ) (z v : A) :
    sourceSectionCovariantDerivative g F W (t, z) (0, v) =
      sourceSectionCovariantDerivative g (fun q => F (t, q)) (fun q => W (t, q)) z v := by
  have hline : (fun r : ℝ => (t, z) + r • (0, v)) = (fun r => (t, z + r • v)) := by
    funext r
    ext <;> simp
  change Geometry.Riemannian.CovariantDerivativeAlong.covDerivAlong g
    (F ∘ (fun r : ℝ => (t, z) + r • (0, v)))
    (fun r => W ((fun r : ℝ => (t, z) + r • (0, v)) r)) 0 = _
  rw [hline]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_parameter_slice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_parameter_slice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_parameter_slice ``Submission.DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_parameter_slice



theorem sourceSectionCovariantDerivative_congr
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : A → M)
    {W Z : ∀ q, TangentSpace 𝓘(ℝ, E) (U q)} {z : A}
    (h : ∀ᶠ q in 𝓝 z, W q = Z q) (v : A) :
    sourceSectionCovariantDerivative g U W z v = sourceSectionCovariantDerivative g U Z z v := by
  apply Geometry.Riemannian.Variation.covDerivAlong_congr_of_eventuallyEq
  have hl : _root_.Filter.Tendsto (fun r : ℝ => z + r • v) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun r : ℝ => z + r • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using hc.tendsto (0 : ℝ)
  exact hl.eventually h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_congr ``Submission.DifferentialGeometry.Geometry.sourceSectionCovariantDerivative_congr

end DifferentialGeometry.Geometry
