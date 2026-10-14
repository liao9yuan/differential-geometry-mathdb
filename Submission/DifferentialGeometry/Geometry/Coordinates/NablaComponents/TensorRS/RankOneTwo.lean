import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Tensor
import Submission.DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.TensorLieDeriv
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff _root_.Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

theorem nablaRS_coordFrame_1_2_of_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (A : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 1 2)
    (x₀ : M)
    (k i j : CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I)
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        1 2 cov X A x₀)
      (upperIdx1 k)
      (lowerIdx2 i j)
    =
      coordDerivRSAt (I := I) (fun x => X x) x₀ (fun x => A x)
        (upperIdx1 k)
        (lowerIdx2 i j)
      +
      ∑ m : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) m k
        *
        coordComponentRSAt (I := I)
          (A x₀)
          (upperIdx1 m)
          (lowerIdx2 i j)
      -
      ∑ m : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) i m
        *
        coordComponentRSAt (I := I)
          (A x₀)
          (upperIdx1 k)
          (lowerIdx2 m j)
      -
      ∑ m : CoordinateIdx (𝕜 := 𝕜) E,
        christoffelAlongInFrame cov
          (coordinateFrameAt (I := I) x₀)
          (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
          x₀ (X x₀) j m
        *
        coordComponentRSAt (I := I)
          (A x₀)
          (upperIdx1 k)
          (lowerIdx2 i m) := by
  classical
  have h := nablaRS_coordFrame_slots_of_smooth
    (I := I) cov X A x₀ (upperIdx1 k) (lowerIdx2 i j)
  rw [h]
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, upperIdx1_apply,
    lowerIdx2_zero, lowerIdx2_one, Function_update_upperIdx1,
    Function_update_lowerIdx2_zero, Function_update_lowerIdx2_one]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.nablaRS_coordFrame_1_2_of_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.nablaRS_coordFrame_1_2_of_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.nablaRS_coordFrame_1_2_of_smooth ``Submission.DifferentialGeometry.Tensor.Coordinates.nablaRS_coordFrame_1_2_of_smooth

end DifferentialGeometry.Tensor.Coordinates
