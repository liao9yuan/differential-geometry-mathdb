import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Derivation.CoordinateRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.CoordinateRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle

open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem coordTowerSmooth
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (x0 : M)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (x : M) (hx : x ∈ chartLeviCivitaGoodSet (I := I) x0)
    (k : Nat) (idx : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        iteratedRmComp (I := I) (coordinateFrameAt (I := I) x0)
          (solutionChristoffelComponents (I := I) S x0) (solutionCurvatureComponents (I := I) S x0)
          k p.1 p.2 idx)
      ((t : Real), x) := by
  have hxframe : x ∈ coordinateFrameSet (I := I) x0 :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  refine iterRmComp_smoothAt (I := I)
    (frame := coordinateFrameAt (I := I) x0)
    (hframe := coordinateFrameAt_isLocalFrame (I := I) x0)
    (hu := coordinateFrameSet_open (I := I) x0) hxframe
    (chr := solutionChristoffelComponents (I := I) S x0)
    (base := solutionCurvatureComponents (I := I) S x0) ?_ ?_ k idx
  · intro i j l
    simpa [solutionChristoffelComponents] using
      coordGammaSmoothInf (I := I) S hS x0 t x hxframe i j l
  · intro slots
    exact coordRmFinSmooth (I := I) hS x0 t x hx slots

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.coordTowerSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.coordTowerSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.coordTowerSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.coordTowerSmooth

end DifferentialGeometry.PDE.RicciFlow
