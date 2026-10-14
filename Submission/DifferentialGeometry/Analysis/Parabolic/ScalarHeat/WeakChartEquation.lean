import Submission.DifferentialGeometry.Analysis.Distribution.WeakEquation
import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.ChartBalance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Analysis.Distribution
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]

theorem hasDerivAt_of_chart_weighted_weak_equation
    {μ : _root_.MeasureTheory.Measure (ℝ × E)} [Measure.IsAddHaarMeasure μ]
    (g : ℝ → SmoothRiemannianMetric I M) (u : ℝ → M → ℝ)
    (α : M) {t r : ℝ} {x : M} (hx : x ∈ (chartAt H α).source)
    {S T : Set (ℝ × E)} (hS : IsOpen S) (hST : S ⊆ T)
    (hpoint : (t, extChartAt I α x) ∈ S)
    (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t))
    (hρ : HasDerivAt
      (fun s => chartDensityOnE (I := I) (g s) α (extChartAt I α x))
      (r * chartDensityOnE (I := I) (g t) α (extChartAt I α x)) t)
    (hweighted : ContDiffOn ℝ 1
      (fun p : ℝ × E => chartDensityOnE (I := I) (g p.1) α p.2 *
        u p.1 ((extChartAt I α).symm p.2)) S)
    (hflux : ∀ i : Fin (Module.finrank ℝ E), ContDiffOn ℝ 1
      (fun p : ℝ × E => chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2) S)
    (hweak : ∀ φ : ℝ × E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ T →
      (∫ p in T, (chartDensityOnE (I := I) (g p.1) α p.2 *
        u p.1 ((extChartAt I α).symm p.2)) * fderiv ℝ φ p (1, 0) ∂μ) =
      ∑ i : Fin (Module.finrank ℝ E), ∫ p in T,
        chartVossWeylIntegrand (I := I) (g p.1) α (u p.1) i p.2 *
          fderiv ℝ φ p (0, chartModelBasis E i) ∂μ) :
    HasDerivAt (fun s => u s x)
      (laplacian (I := I) (LeviCivita (I := I) (g t)) (g t) (u t) x -
        r * u t x) t := by
  apply hasDerivAt_of_chart_spacetime_heat_balance g u α hx hu hρ
  · exact (hweighted.differentiableOn one_ne_zero _ hpoint).differentiableAt
      (hS.mem_nhds hpoint)
  · intro i
    exact ((hflux i).differentiableOn one_ne_zero _ hpoint).differentiableAt
      (hS.mem_nhds hpoint)
  · exact fderiv_eq_sum_of_weak_equation_on_superset Finset.univ hS hST
      (1, 0) (fun i => (0, chartModelBasis E i)) hweighted (fun i _ => hflux i)
      hweak _ hpoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_chart_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_chart_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_chart_weighted_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_chart_weighted_weak_equation

end DifferentialGeometry.Analysis.Parabolic
