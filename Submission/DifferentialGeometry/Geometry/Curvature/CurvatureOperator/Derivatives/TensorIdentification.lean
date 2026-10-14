import Submission.DifferentialGeometry.Geometry.Connection.MetricCompatibility.Commutation.SecondOrder
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Slotwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    nablaTensorCurvSec (I := I) g
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Y b) (fun b => Z b) A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv ``Submission.DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv

omit [CompleteSpace E] in
theorem nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        nablaTensorCurvSec (I := I) g
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun b => Z b) A x =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A x :=
  Finset.sum_congr rfl fun i _ =>
    nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv (I := I) g s
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) Z A x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum ``Submission.DifferentialGeometry.Geometry.Curvature.nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum

end Curvature
end Geometry
end DifferentialGeometry
