import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.WeakChartEquation
import Submission.DifferentialGeometry.Geometry.Metric.Family.ChartHeatRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Parabolic

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

theorem hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation
    {μ : _root_.MeasureTheory.Measure (ℝ × E)} [Measure.IsAddHaarMeasure μ]
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) {J : Set ℝ} (hJ : IsOpen J)
    (hJreg : J ⊆ D.regular) {u : ℝ → M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2) (J ×ˢ _root_.Set.univ))
    (α : M) {t r : ℝ} (ht : t ∈ J) {x : M}
    (hx : x ∈ (chartAt H α).source) {T : Set (ℝ × E)}
    (hT : J ×ˢ interior (extChartAt I α).target ⊆ T)
    (hρ : HasDerivAt
      (fun s => chartDensityOnE (I := I) (g s) α (extChartAt I α x))
      (r * chartDensityOnE (I := I) (g t) α (extChartAt I α x)) t)
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
  have hxext : x ∈ (extChartAt I α).source := by
    rwa [extChartAt_source_eq_chartAt_source (I := I)]
  have hxtarget : extChartAt I α x ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hxext
  have huslice : ContMDiff I 𝓘(ℝ, ℝ) ∞ (u t) :=
    hu.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y => ⟨ht, _root_.Set.mem_univ y⟩)
  apply hasDerivAt_of_chart_weighted_weak_equation (μ := μ) g u α hx
    (hJ.prod isOpen_interior) hT ⟨ht, hxtarget⟩ huslice hρ
  · exact (chartDensity_mul_scalar_contDiffOn_of_metricFamilySmoothOn hg hJreg hu α).of_le
      (by simp)
  · intro i
    exact (chartVossWeylIntegrand_contDiffOn_of_metricFamilySmoothOn hg hJreg
      hJ.uniqueDiffOn hu α i).of_le (by simp)
  · exact hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.hasDerivAt_of_metricFamilySmoothOn_chart_weak_equation

end DifferentialGeometry.Analysis.Parabolic
