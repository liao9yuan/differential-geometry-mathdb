import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessBallCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ShiUniformConstant
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M]

variable [NeZero (Module.finrank ℝ E)]

theorem scalarLaplacianCurvatureJetBound :
    ScalarLaplacianCurvatureJetBound.{u, uE, uH} I ((Module.finrank ℝ E : ℝ) ^ 6) := by
  intro M _ _ _ _ _ _ _ D S _ t _ x
  exact abs_laplacian_scalar_le_second_curvature S t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.scalarLaplacianCurvatureJetBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.scalarLaplacianCurvatureJetBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.scalarLaplacianCurvatureJetBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.scalarLaplacianCurvatureJetBound

theorem goodPointBoundsOn_of_modelBound [I.Boundaryless] {kappa : ℝ}
    (hmod : ModelCurvatureBoundNearBase.{u, uE, uH} I kappa) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
        [VectorBundle ℝ E (TangentSpace I : M → Type _)]
        {T : ℝ} {hT : (0 : ℝ) < T}
        (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
        IsSolutionOn (I := I) S → ∀ (x : M) (t eps : ℝ), 0 < eps → eps ≤ 1 / 4 →
          IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
            (∀ v : TangentSpace I x,
                |scalarDifferential (I := I) S t x v| ≤
                  2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
                    Real.sqrt ((S.base.metric t).inner x v v)) ∧
              |deriv (fun tau : ℝ => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2 :=
  goodPointBoundsOn_of_modelCurvatureBound I (by positivity) hmod
    witnessSourceBallCapture (localShiUniformConstant I) scalarLaplacianCurvatureJetBound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.goodPointBoundsOn_of_modelBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.goodPointBoundsOn_of_modelBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.goodPointBoundsOn_of_modelBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.goodPointBoundsOn_of_modelBound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
