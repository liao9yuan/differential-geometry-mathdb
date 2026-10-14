import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.ScalarTrace
import Submission.DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import Submission.DifferentialGeometry.Analysis.Calculus.PartialDerivative.Parameter
import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.JointSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.BigOperators

namespace DifferentialGeometry.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

theorem chartScalar_contDiffOn_of_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, (g z.1).inner z.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (_root_.Set.univ : Set M)))
    (p : M) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E =>
      scalarOnE (I := I) p (fun x => metricScalarAt (g z.1) x) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  have hgram := chartGramFamilySmoothWithinOn_of_contMDiffOn g p
    (chartGramMatrix_joint_contMDiffOn g J hg p)
  have hricci (i j : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (fun z : ℝ × E => chartRicciTensor (g z.1) p i j z.2)
        (J ×ˢ interior (extChartAt I p).target) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact chartRicciTensor_contDiffWithinAt g p hgram i j ht hy
  have htrace : ContDiffOn ℝ ∞
      (fun z : ℝ × E => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramOnE (g z.1) p i j z.2 * chartRicciTensor (g z.1) p i j z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      (chartInvGramOnE_contDiffOn_of_contMDiffOn g hg p i j).mul (hricci i j)
  have hscalar : ContDiffOn ℝ ∞
      (fun z : ℝ × E => scalarOnE (I := I) p (fun x => metricScalarAt (g z.1) x) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
    apply htrace.congr
    rintro ⟨t, y⟩ ⟨_, hy⟩
    have hx : (extChartAt I p).symm y ∈ chartLeviCivitaGoodSet (I := I) p := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
      exact (extChartAt I p).map_target (interior_subset hy)
    change metricScalarAt (g t) ((extChartAt I p).symm y) = _
    rw [DifferentialGeometry.PDE.RicciFlow.metricScalar_chartTrace_eq (g t) p hx]
    simp only [(extChartAt I p).right_inv (interior_subset hy)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simpa only [(extChartAt I p).right_inv (interior_subset hy)] using
      ricciTensor_chartBasisVec_alpha_eq (g t) p i j hx
  exact hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartScalar_contDiffOn_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartScalar_contDiffOn_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartScalar_contDiffOn_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.chartScalar_contDiffOn_of_contMDiffOn

theorem chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, (g z.1).inner z.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (_root_.Set.univ : Set M)))
    (p : M) :
    ContinuousOn (fun z : ℝ × E => fderiv ℝ
      (scalarOnE (I := I) p (fun x => metricScalarAt (g z.1) x)) z.2)
      (J ×ˢ interior (extChartAt I p).target) := by
  exact ((chartScalar_contDiffOn_of_contMDiffOn g hg p).fderiv_snd
    (G := fun t => scalarOnE (I := I) p (fun x => metricScalarAt (g t) x))
    isOpen_interior (m := 0) (by simp)).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Curvature.chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn

end DifferentialGeometry.Geometry.Curvature

end
