import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [I.Boundaryless] [T2Space M]

theorem SolutionOn.scalar_chartTrace_eq
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (p : M) {y : E} (hy : y ∈ (extChartAt I p).target) :
    S.scalar t ((extChartAt I p).symm y) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (S.base.metric t) p i j y *
          chartRicciTensor (I := I) (S.base.metric t) p i j y := by
  have hx : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact (extChartAt I p).map_target hy
  change metricScalarAt (I := I) (S.base.metric t) ((extChartAt I p).symm y) = _
  rw [metricScalar_chartTrace_eq (S.base.metric t) p hx]
  simp only [(extChartAt I p).right_inv hy]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simpa only [(extChartAt I p).right_inv hy] using
    ricciTensor_chartBasisVec_alpha_eq (S.base.metric t) p i j hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_chartTrace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_chartTrace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_chartTrace_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_chartTrace_eq

end DifferentialGeometry.PDE.RicciFlow
