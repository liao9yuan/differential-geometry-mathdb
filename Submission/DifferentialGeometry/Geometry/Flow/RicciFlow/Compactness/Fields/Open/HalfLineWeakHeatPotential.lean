import Submission.DifferentialGeometry.Analysis.Parabolic.ScalarHeat.WeakPotential
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineTimeReversal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineVolumeDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.BigOperators _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} (Φ : PointedCGHMaps (I := I) X P subseq)
  {R : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    SmoothRiemannianMetric I P.M}
  {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ}
  {htgt : TargetIsSigmaCompact Φ}
  (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)

theorem isHeatPotOn_time_sub_of_chart_weighted_weak_equation
    {μ : _root_.MeasureTheory.Measure (ℝ × E)} [Measure.IsAddHaarMeasure μ]
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular) (a : ℝ) (D : RealTimeInterval)
    {J : Set ℝ} (hJ : IsOpen J) (hJa : J ⊆ _root_.Set.Ioi a) (hcarrier : D.carrier ⊆ J)
    (u : ℝ → P.M → ℝ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × P.M => u p.1 p.2) (J ×ˢ _root_.Set.univ) →
    (∀ α : P.M, ∀ φ : ℝ × E → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ interior (extChartAt I α).target →
      (∫ p in J ×ˢ interior (extChartAt I α).target,
        (chartDensityOnE (I := I) (co.gInf (a - p.1)) α p.2 *
          u p.1 ((extChartAt I α).symm p.2)) * fderiv ℝ φ p (1, 0) ∂μ) =
      ∑ i : Fin (Module.finrank ℝ E), ∫ p in J ×ˢ interior (extChartAt I α).target,
        chartVossWeylIntegrand (I := I) (co.gInf (a - p.1)) α (u p.1) i p.2 *
          fderiv ℝ φ p (0, chartModelBasis E i) ∂μ) →
    let G : MetricConnectionFamily (I := I) (M := P.M) ℝ :=
      { metric := fun t => co.gInf (a - t)
        connection := fun t => leviCivitaConnectionOfMetric (I := I) (co.gInf (a - t))
        metricCompatible := fun t =>
          leviCivitaConnectionOfMetric_isMetricCompatible (I := I) (co.gInf (a - t)) }
    IsHeatPotOn D G (fun t x => -metricScalarAt (co.gInf (a - t)) x) u := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  intro hu hweak G
  let Dg : RealTimeInterval := RealTimeInterval.openInfinite a (a + 1) (lt_add_one a)
  have hg : MetricFamilySmoothOn Dg G.metric :=
    co.metric_smooth_time_sub (Φ := Φ) hreg a (by exact Subset.rfl)
  apply IsHeatPotOn.of_chart_weighted_weak_equation (μ := μ) G hg hJ hJa hcarrier
    (fun _ _ => rfl) hu
  · intro t ht x
    have hxbase : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact mem_chart_source H x
    have hd := co.hasDerivAt_chartDensity_time_sub Φ hreg
      (hJa (hcarrier (D.regular_subset ht))) x hxbase
    have hleft : (extChartAt I x).symm (extChartAt I x x) = x :=
      (extChartAt I x).left_inv (by
        rw [extChartAt_source_eq_chartAt_source (I := I)]
        exact mem_chart_source H x)
    simpa only [chartDensityOnE, hleft] using hd
  · exact hweak

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isHeatPotOn_time_sub_of_chart_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isHeatPotOn_time_sub_of_chart_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isHeatPotOn_time_sub_of_chart_weighted_weak_equation ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.isHeatPotOn_time_sub_of_chart_weighted_weak_equation

end DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData
