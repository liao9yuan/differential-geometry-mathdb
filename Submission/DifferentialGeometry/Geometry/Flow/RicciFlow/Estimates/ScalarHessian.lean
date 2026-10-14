import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.NormBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem normSq_scalarHess_le_second_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    normSq0S (S.base.metric t) x 2
      (hessianSec (I := I) (S.base.connection t)
        (metricCov_smooth (S.base.metric t))
        (S.scalar t) (scalarSmoothOfSolution S t) x) ≤
      (Module.finrank ℝ E : ℝ) ^ 10 * nablaKRm04NormSqIntrinsic S 2 t x := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let g := S.base.metric t
  let Ric := metricRicci (I := I) g
  have hHess := normSq_hessian_metricTrace_le g Ric x
  have hRic := ricTower_normSq_le S t 2 x
  change normSq0S g x 4 (iterCov g 2 Ric 2 x) ≤
    (Module.finrank ℝ E : ℝ) ^ 6 * nablaKRm04NormSqIntrinsic S 2 t x at hRic
  change normSq0S g x 2
      (hessianSec (I := I) (S.base.connection t)
        (metricCov_smooth g) (S.scalar t) (scalarSmoothOfSolution S t) x) ≤
    (Module.finrank ℝ E : ℝ) ^ 4 * normSq0S g x 4 (iterCov g 2 Ric 2 x) at hHess
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 4 * normSq0S g x 4 (iterCov g 2 Ric 2 x) := hHess
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 4 *
        ((Module.finrank ℝ E : ℝ) ^ 6 * nablaKRm04NormSqIntrinsic S 2 t x) :=
      mul_le_mul_of_nonneg_left hRic (by positivity)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.normSq_scalarHess_le_second_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.normSq_scalarHess_le_second_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.normSq_scalarHess_le_second_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.normSq_scalarHess_le_second_curvature

theorem sqrt_normSq_scalarHess_le_second_curvature
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    Real.sqrt (normSq0S (S.base.metric t) x 2
      (hessianSec (I := I) (S.base.connection t)
        (metricCov_smooth (S.base.metric t))
        (S.scalar t) (scalarSmoothOfSolution S t) x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 5 *
        Real.sqrt (nablaKRm04NormSqIntrinsic S 2 t x) := by
  have hbound := Real.sqrt_le_sqrt (normSq_scalarHess_le_second_curvature S t x)
  have hp : (Module.finrank ℝ E : ℝ) ^ 10 = ((Module.finrank ℝ E : ℝ) ^ 5) ^ 2 := by
    ring
  rwa [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.sqrt_normSq_scalarHess_le_second_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.sqrt_normSq_scalarHess_le_second_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.sqrt_normSq_scalarHess_le_second_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.sqrt_normSq_scalarHess_le_second_curvature

end DifferentialGeometry.PDE.RicciFlow
