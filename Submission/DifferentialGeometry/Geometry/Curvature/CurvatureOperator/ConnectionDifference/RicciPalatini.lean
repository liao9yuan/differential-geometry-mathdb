import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ConnectionDifference.Curvature
import Submission.DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] [T2Space M] in
theorem connectionDifference_eq_difference (g₀ g₁ : SmoothRiemannianMetric I M) :
    connectionDifference (I := I) g₁ g₀ =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.connectionDifference_eq_difference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.connectionDifference_eq_difference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.connectionDifference_eq_difference ``Submission.DifferentialGeometry.Geometry.Curvature.connectionDifference_eq_difference
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
def covDerivConnectionDifference (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) : TangentSpace I x :=
  covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference ``Submission.DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] [T2Space M] in
theorem covDerivConnectionDifference_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    covDerivConnectionDifference (I := I) g₀ g₁ X Y Z x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_eq ``Submission.DifferentialGeometry.Geometry.Curvature.covDerivConnectionDifference_eq

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem ricciTensor_sub_eq_connectionDifference_palatini (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I) g₁ x v w - ricciTensor (I := I) g₀ x v w =
      ∑ i : Fin (Module.finrank ℝ E),
        (DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x).repr
          ((covDerivConnectionDifference (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x) i))
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x w) x
              - covDerivConnectionDifference (I := I) g₀ g₁
                (smoothExtensionTangent (I := I) x v)
                (smoothExtensionTangent (I := I) x ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x) i))
                (smoothExtensionTangent (I := I) x w) x)
            + (connectionDifference (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x v)
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x
                    ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x) i) x)
                - connectionDifference (I := I) g₁ g₀ x
                  (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
                    (smoothExtensionTangent (I := I) x
                      ((DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis (I := I) x) i))
                    (smoothExtensionTangent (I := I) x w) x)
                  (smoothExtensionTangent (I := I) x v x))) i :=
  ricciTensor_sub_eq_basisSum_difference (I := I) g₀ g₁ x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_sub_eq_connectionDifference_palatini then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_sub_eq_connectionDifference_palatini"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_sub_eq_connectionDifference_palatini ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_sub_eq_connectionDifference_palatini

end Curvature
end Geometry
end DifferentialGeometry
