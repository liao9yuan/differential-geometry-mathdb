import Submission.DifferentialGeometry.Geometry.Connection.MetricTrace.Relowering
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Relowering

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Connection

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem covariant_divergence_relowering_defect
    (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) :
    covDiv0SField (I := I) g₁
        (reLower (I := I) g₂ g₁ (metricNabla0S (I := I) g₁ T) -
          metricNabla0S (I := I) g₁ T) =
      (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ T) -
        roughLap0SField (I := I) g₁ T) +
      metricTraceFirstTwoField (I := I) g₁
        (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ T)
          (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂))) := by
  have hmetric : metricNabla0S (I := I) g₁ (metricTensorField (I := I) g₂) =
      lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂) := by
    rw [lapDiffFlux, metricNabla0S_self, sub_zero]
  rw [covDiv0SField_sub, covDiv0SField, nabla_reLower, metricTraceFirstTwoField_add,
    trace_reLower, hmetric]
  change (reLower (I := I) g₂ g₁ (roughLap0SField (I := I) g₁ T) +
    metricTraceFirstTwoField (I := I) g₁
      (reLowerPair (I := I) g₁ (metricNabla0S (I := I) g₁ T)
        (lapDiffFlux (I := I) g₁ g₂ (metricTensorField (I := I) g₂)))) -
      roughLap0SField (I := I) g₁ T = _
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covariant_divergence_relowering_defect then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covariant_divergence_relowering_defect"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covariant_divergence_relowering_defect ``Submission.DifferentialGeometry.Geometry.Connection.covariant_divergence_relowering_defect

end DifferentialGeometry.Geometry.Connection
