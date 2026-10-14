import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.Ricci
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem metricScalar_chartTrace_eq
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    metricScalarAt (I := I) g x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i j (extChartAt I α x) *
          ricciTensor (I := I) g x
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x) := by
  have hbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hxsrc : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hgram : ∀ k l : Fin (Module.finrank ℝ E),
      g.inner x (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hbase k) (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hbase l)
        = DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α x k l := by
    intro k l
    rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply, DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply]
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply (I := I) g α x k l).symm
  have hinv : Tensor0SBundle.MetricInverseInBasis (I := I) g x
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hbase)
      (fun k l => chartInvGramMatrix (I := I) g α x k l) := by
    intro i j
    refine ⟨?_, ?_⟩
    · simp only [hgram]
      rw [← Matrix.mul_apply, chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hbase,
        Matrix.one_apply]
    · simp only [hgram]
      rw [← Matrix.mul_apply, chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase,
        Matrix.one_apply]
  have htrace := DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
    (I := I) g (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hbase)
    (fun k l => chartInvGramMatrix (I := I) g α x k l) hinv (metricRicciAt (I := I) g x)
  unfold metricScalarAt
  rw [htrace]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [chartInvGramOnE_def, (extChartAt I α).left_inv hxsrc, DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply,
    DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply]
  congr 1
  exact metricRicciAt_apply_eq_ricciTensor (I := I) g x
    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq

end DifferentialGeometry.PDE.RicciFlow
