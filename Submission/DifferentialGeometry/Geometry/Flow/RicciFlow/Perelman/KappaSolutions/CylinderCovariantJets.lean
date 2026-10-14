import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderConnection
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff


theorem shrinkingCylinder_metricCovDerivStep_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1) (a : ℕ)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := SpatialNeckCylinder) (n := ∞) (a + 2)) :
    metricCovDerivStep (scalarOneShrinkingCylinderMetric s hs) a A =
      metricCovDerivStep (scalarOneShrinkingCylinderMetric t ht) a A := by
  apply ContMDiffSection.ext
  intro x
  rw [metricCovDerivStep_apply, metricCovDerivStep_apply]
  unfold totalNabla0SFun
  rw [shrinkingCylinder_connectionEndomorphism_eq s t hs ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_metricCovDerivStep_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_metricCovDerivStep_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_metricCovDerivStep_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_metricCovDerivStep_eq


theorem shrinkingCylinder_tensor02CovDeriv_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := SpatialNeckCylinder) (n := ∞) 2) (a : ℕ) :
    tensor02CovDeriv A (scalarOneShrinkingCylinderMetric s hs) a =
      tensor02CovDeriv A (scalarOneShrinkingCylinderMetric t ht) a := by
  have hstep :
      (fun (b : ℕ) (B : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := SpatialNeckCylinder) (n := ∞) (b + 2)) =>
          metricCovDerivStep (scalarOneShrinkingCylinderMetric s hs) b B) =
      (fun (b : ℕ) (B : Tensor0SField (I := SpatialNeckCylinderModel)
        (M := SpatialNeckCylinder) (n := ∞) (b + 2)) =>
          metricCovDerivStep (scalarOneShrinkingCylinderMetric t ht) b B) := by
    funext b B
    exact shrinkingCylinder_metricCovDerivStep_eq s t hs ht b B
  unfold tensor02CovDeriv
  rw [hstep]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDeriv_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDeriv_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDeriv_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDeriv_eq


theorem shrinkingCylinder_tensor02CovDerivNormWith_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (A : Tensor0SField (I := SpatialNeckCylinderModel)
      (M := SpatialNeckCylinder) (n := ∞) 2) (a : ℕ)
    (gNorm : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder)
    (x : SpatialNeckCylinder) :
    tensor02CovDerivNormWith a A (scalarOneShrinkingCylinderMetric s hs) gNorm x =
      tensor02CovDerivNormWith a A (scalarOneShrinkingCylinderMetric t ht) gNorm x := by
  rw [tensor02CovDerivNormWith, tensor02CovDerivNormWith,
    shrinkingCylinder_tensor02CovDeriv_eq s t hs ht]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDerivNormWith_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDerivNormWith_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDerivNormWith_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.shrinkingCylinder_tensor02CovDerivNormWith_eq

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
