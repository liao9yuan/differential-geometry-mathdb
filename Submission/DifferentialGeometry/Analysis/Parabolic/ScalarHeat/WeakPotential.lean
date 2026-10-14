import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.SmoothMetricWeakEquation
import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.SmoothPotential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn

open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

theorem of_chart_weighted_weak_equation
    {μ : _root_.MeasureTheory.Measure (ℝ × E)} [Measure.IsAddHaarMeasure μ]
    {D Dg : RealTimeInterval}
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (hg : MetricFamilySmoothOn Dg G.metric) {J : Set ℝ} (hJ : IsOpen J)
    (hJreg : J ⊆ Dg.regular) (hcarrier : D.carrier ⊆ J)
    (hconnection : ∀ t ∈ D.regular, G.connection t = LeviCivita (I := I) (G.metric t))
    {R u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (J ×ˢ _root_.Set.univ))
    (hρ : ∀ t ∈ D.regular, ∀ x : M,
      HasDerivAt
        (fun s => chartDensityOnE (I := I) (G.metric s) x (extChartAt I x x))
        (R t x * chartDensityOnE (I := I) (G.metric t) x (extChartAt I x x)) t)
    (hweak : ∀ α : M, ∀ φ : ℝ × E → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ interior (extChartAt I α).target →
      (∫ p in J ×ˢ interior (extChartAt I α).target,
        (chartDensityOnE (I := I) (G.metric p.1) α p.2 *
          u p.1 ((extChartAt I α).symm p.2)) * fderiv ℝ φ p (1, 0) ∂μ) =
      ∑ i : Fin (Module.finrank ℝ E), ∫ p in J ×ˢ interior (extChartAt I α).target,
        chartVossWeylIntegrand (I := I) (G.metric p.1) α (u p.1) i p.2 *
          fderiv ℝ φ p (0, chartModelBasis E i) ∂μ) :
    IsHeatPotOn D G (fun t x => -R t x) u := by
  apply of_contMDiffOn hu hcarrier
  intro t ht x
  have heq := hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation (μ := μ)
    hg hJ hJreg hu x (hcarrier (D.regular_subset ht)) (mem_chart_source H x)
    Subset.rfl (hρ t ht x) (hweak x)
  simpa only [laplacianAt, hconnection t ht, sub_eq_add_neg, neg_mul] using heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_chart_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_chart_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_chart_weighted_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn.of_chart_weighted_weak_equation

end DifferentialGeometry.Analysis.Parabolic.IsHeatPotOn
