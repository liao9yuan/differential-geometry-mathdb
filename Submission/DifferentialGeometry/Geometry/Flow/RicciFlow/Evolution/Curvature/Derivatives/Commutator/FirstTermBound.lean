import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Commutator.Bound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Frame.Orthonormal
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

omit [Module.Finite ℝ E] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem nablaLapComm_T1_eq_covDerivK
    [FiniteDimensional Real E]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (t : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.RegularTime D)
    (x₀ : M)
    (a b c : CoordinateIdx (𝕜 := Real) E) (m : Fin 4 → CoordinateIdx (𝕜 := Real) E) :
    nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a b c m) -
      nabla3Rm04Field (I := I) S (t : Real) x₀
        (nabla3FrameTuple (I := I) (coordinateFrameAt (I := I) x₀) x₀ a c b m) =
      mvfderiv (I := I)
          (fun p : M =>
            curvatureAction0SAt (I := I) (S.base.rm13 (t : Real))
              (S.base.rm04 (t : Real) p)
              (coordinateFrameAt (I := I) x₀ b p) (coordinateFrameAt (I := I) x₀ c p)
              (frameTuple (I := I) (coordinateFrameAt (I := I) x₀) p m))
          x₀ (coordinateFrameAt (I := I) x₀ a x₀) -
        ∑ q : Fin 6,
          curvatureAction0SAt (I := I) (S.base.rm13 (t : Real)) (S.base.rm04 (t : Real) x₀)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 0)
            (nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q 1)
            (fun r : Fin 4 =>
              nabla3CorrectedSlots (I := I) S (t : Real) x₀ a b c m q (Fin.succ (Fin.succ r))) :=
  nablaLapComm_T1_eq_covDeriv_curvatureAction (I := I) S t x₀ a b c m

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_T1_eq_covDerivK then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.nablaLapComm_T1_eq_covDerivK"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.nablaLapComm_T1_eq_covDerivK ``Submission.DifferentialGeometry.PDE.RicciFlow.nablaLapComm_T1_eq_covDerivK

end DifferentialGeometry.PDE.RicciFlow
