import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Local
import Submission.DifferentialGeometry.Geometry.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

theorem localPullMetric_scaleMetric [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M → N)
    (hΦ : IsLocalDiffeomorph I J ∞ Φ) (c : ℝ) (hc : 0 < c) :
    localPullMetric (scaleMetric c hc g) Φ hΦ =
      scaleMetric c hc (localPullMetric g Φ hΦ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [localPullMetric_inner, scaleMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.localPullMetric_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.localPullMetric_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.localPullMetric_scaleMetric ``Submission.DifferentialGeometry.localPullMetric_scaleMetric


theorem Diffeomorph.pullbackMetricCross_scaleMetric
    [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (c : Real) (hc : 0 < c) :
    Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ =
      scaleMetric c hc (Diffeomorph.pullbackMetricCross g Φ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.pullbackMetricCross_scaleMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.pullbackMetricCross_scaleMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.pullbackMetricCross_scaleMetric ``Submission.DifferentialGeometry.Diffeomorph.pullbackMetricCross_scaleMetric

theorem Diffeomorph.inner_sqrt_smul_mfderiv [T2Space M]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (c : Real) (hc : 0 < c) (x : M) (v w : TangentSpace I x) :
    g.inner (Φ x) (Real.sqrt c • mfderiv I J Φ x v)
      (Real.sqrt c • mfderiv I J Φ x w) =
        (Diffeomorph.pullbackMetricCross (scaleMetric c hc g) Φ).inner x v w := by
  rw [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, Real.mul_self_sqrt hc.le]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Diffeomorph.inner_sqrt_smul_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Diffeomorph.inner_sqrt_smul_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Diffeomorph.inner_sqrt_smul_mfderiv ``Submission.DifferentialGeometry.Diffeomorph.inner_sqrt_smul_mfderiv

end DifferentialGeometry
