import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1Regularity
import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.Sobolev
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Regularity.CarrierC1
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.StrictRefinement
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CarrierC1RegularityAbsolutelyContinuous
import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothnessScalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [TopologicalSpace.PseudoMetrizableSpace M] {D : RealTimeInterval}

theorem lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (hab : a < b) (gamma : ℝ → M)
    (hgamma : Manifold.absolutelyContinuousOnInterval I gamma a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T gamma) _root_.MeasureTheory.MeasureSpace.volume a b)
    (U : Set ℝ) (hU : U ⊆ D.carrier)
    (htime : ∀ r ∈ _root_.Set.Icc a b, T - r ^ 2 ∈ U)
    (hreg : ∀ r ∈ _root_.Set.Ioo a b, T - r ^ 2 ∈ D.regular)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun z : ℝ × M => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (U ×ˢ (_root_.Set.univ : Set M)))
    (hmin : ∀ delta : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (_root_.Set.Icc a b) := by
  apply lMinCurve_c1_of_absolutelyContinuousOnInterval_of_spatial_derivatives
    S hS T a b hab gamma hgamma hint U hU htime hreg _ _ hmin
  · intro p
    apply chartGramOp_spatial_fderiv_continuousOn S.family p
      (fun _ hz => interior_subset hz.2)
    intro i j
    have hh := chartGramOnE_contDiffOn_of_contMDiffOn S.base.metric hmetric p i j
    exact (hh.iteratedFDeriv_snd
      (G := fun t y => chartGramOnE (S.base.metric t) p i j y)
      isOpen_interior 1 (m := 0) (by simp)).continuousOn
  · intro p
    exact chartScalar_spatial_fderiv_continuousOn_of_contMDiffOn S.base.metric hmetric p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lMinCurve_c1_of_absolutelyContinuousOnInterval_of_jointContMDiffOn_metric

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
