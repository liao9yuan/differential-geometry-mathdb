import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Basic
import Submission.DifferentialGeometry.Bundle.VectorField.LieBracket
import Submission.DifferentialGeometry.Bundle.VectorField.Pushforward
import Submission.DifferentialGeometry.Geometry.Metric.LieDerivative.Cartan
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.CovariantDerivative.Pointwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

open _root_.Submission.DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise
    (g : SmoothRiemannianMetric I M)
    (Φ : M ≃ₘ⟮I, I⟯ M)
    (Y : ∀ x : M, TangentSpace I x)
    (hY_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)))
    (hPush_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x
        (Diffeomorph.pushforward Φ Y x)))
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) (Diffeomorph.pullbackMetric g Φ)
        ⟨Y, hY_smooth⟩ x v w
      = lieDerivMetric (I := I) g
          ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
            (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  rw [cartan_formula_for_lie_deriv_metric (I := I)
    (Diffeomorph.pullbackMetric g Φ) ⟨Y, hY_smooth⟩ x v w]
  rw [cartan_formula_for_lie_deriv_metric (I := I) g
    ⟨Diffeomorph.pushforward Φ Y, hPush_smooth⟩ (Φ x)
    (mfderiv I I (⇑Φ) x v) (mfderiv I I (⇑Φ) x w)]
  change (Diffeomorph.pullbackMetric g Φ).inner x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x v) w
      + (Diffeomorph.pullbackMetric g Φ).inner x v
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x w)
    = g.inner (Φ x) ((LeviCivita (I := I) g)
        (Diffeomorph.pushforward Φ Y) (Φ x) (mfderiv I I (⇑Φ) x v))
        (mfderiv I I (⇑Φ) x w)
      + g.inner (Φ x) (mfderiv I I (⇑Φ) x v) ((LeviCivita (I := I) g)
        (Diffeomorph.pushforward Φ Y) (Φ x) (mfderiv I I (⇑Φ) x w))
  rw [Diffeomorph.pullbackMetric_inner (I := I) g Φ x
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x v) w,
      Diffeomorph.pullbackMetric_inner (I := I) g Φ x v
        ((LeviCivita (I := I) (Diffeomorph.pullbackMetric g Φ)) Y x w)]
  have hinfty : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hY_mdiff : MDifferentiableAt I I.tangent
      (fun y : M => (TotalSpace.mk' E y (Y y) : TangentBundle I M)) x :=
    (hY_smooth x).mdifferentiableAt hinfty
  rw [LeviCivita_covariantDerivative_pullback_pointwise (I := I) g Φ v
    hY_mdiff,
      LeviCivita_covariantDerivative_pullback_pointwise (I := I) g Φ w
        hY_mdiff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Pullback.lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Pullback.lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Pullback.lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise ``Submission.DifferentialGeometry.PDE.RicciFlow.Pullback.lie_derivative_metric_pullback_natural_under_diffeomorphism_pointwise

end DifferentialGeometry.PDE.RicciFlow.Pullback
