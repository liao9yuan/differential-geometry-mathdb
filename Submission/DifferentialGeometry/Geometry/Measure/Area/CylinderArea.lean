import Submission.DifferentialGeometry.Geometry.Measure.Area.GeodesicAnnulus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.Topology
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry


def cylinderLift {Q : Type*} (H : ℝ × loopCircle → Q) (z : ℂ) : Q :=
  H (z.re, (z.im : loopCircle))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderLift ``Submission.DifferentialGeometry.Geometry.cylinderLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]


def cylinderArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (H : ℝ × loopCircle → M) : ℝ :=
  riemannianArea g (cylinderLift H) unitSquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderArea ``Submission.DifferentialGeometry.Geometry.cylinderArea

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [CompactSpace M] in
theorem cylinderLift_riemannian_lipschitz
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {H : ℝ × loopCircle → M} {K : ℝ≥0}
    (hH : ∀ p q, riemannianEDistOf g (H p) (H q) ≤ (K : ℝ≥0∞) * _root_.EDist.edist p q) :
    ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (cylinderLift H z) (cylinderLift H w) ≤ (C : ℝ≥0∞) * _root_.EDist.edist z w := by
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hH' : LipschitzWith K H := hH
  exact ⟨_, hH'.comp (Complex.reCLM.lipschitz.prodMk
    (loopCircle_projection_lipschitz.comp Complex.imCLM.lipschitz))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.cylinderLift_riemannian_lipschitz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.cylinderLift_riemannian_lipschitz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.cylinderLift_riemannian_lipschitz ``Submission.DifferentialGeometry.Geometry.cylinderLift_riemannian_lipschitz


theorem geodesicAnnulusArea_eq_cylinderArea
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : loopCircle → M) :
    geodesicAnnulusArea g γ₀ γ₁ = cylinderArea g (geodesicAnnulus g γ₀ γ₁) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.geodesicAnnulusArea_eq_cylinderArea then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.geodesicAnnulusArea_eq_cylinderArea"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.geodesicAnnulusArea_eq_cylinderArea ``Submission.DifferentialGeometry.Geometry.geodesicAnnulusArea_eq_cylinderArea

end DifferentialGeometry.Geometry
