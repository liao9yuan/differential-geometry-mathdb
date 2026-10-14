import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic
import Submission.DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve

namespace DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem covAlong_diff
    (g₁ g₂ : SmoothRiemannianMetric I M) (gamma : Real → M)
    (V : ∀ r, TangentSpace I (gamma r)) (t : Real)
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma t) :
    covDerivAlong (I := I) g₁ gamma V t -
        covDerivAlong (I := I) g₂ gamma V t =
      (CovariantDerivative.difference
        (metricCov (I := I) g₁) (metricCov (I := I) g₂) (gamma t))
        (V t)
        ((mfderiv (modelWithCornersSelf Real Real) I gamma t :
          Real →L[Real] TangentSpace I (gamma t)) (1 : Real)) := by
  classical
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
    (gamma t) (V t)
  let W : ∀ r, TangentSpace I (gamma r) := fun r ↦ Y (gamma r)
  have hrep : chartRepAt (I := I) gamma V t t =
      chartRepAt (I := I) gamma W t t := by
    simp only [chartRepAt_apply, W, hY]
  have hfield :
      covDerivAlong (I := I) g₁ gamma V t -
          covDerivAlong (I := I) g₂ gamma V t =
        covDerivAlong (I := I) g₁ gamma W t -
          covDerivAlong (I := I) g₂ gamma W t := by
    simp only [covDerivAlong_def, ← map_sub]
    congr 1
    simp only [chartCovDerivAlong_def]
    rw [hrep]
    abel
  rw [hfield, covAlong_sec (I := I) g₁ gamma Y t hgamma,
    covAlong_sec (I := I) g₂ gamma Y t hgamma]
  have hdiff := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
    (I := I) g₁ g₂ Y.mdifferentiableAt
    ((mfderiv (modelWithCornersSelf Real Real) I gamma t :
      Real →L[Real] TangentSpace I (gamma t)) (1 : Real))
  simpa only [DifferentialGeometry.PDE.DeTurck.connectionDifference, metricCov,
    LeviCivita, hY] using hdiff.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covAlong_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covAlong_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covAlong_diff ``Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong.covAlong_diff

end DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
