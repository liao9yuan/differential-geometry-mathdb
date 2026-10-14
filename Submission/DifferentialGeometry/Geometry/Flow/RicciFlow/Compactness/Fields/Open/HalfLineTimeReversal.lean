import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity
import Submission.DifferentialGeometry.Geometry.Metric.Family.JointSmoothness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)}
  {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}
  {Φ : PointedCGHMaps (I := I) X P subseq}

theorem HalfLineMetricConvergenceData.metric_smooth_time_sub
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ}
    {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (co : HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt)
    (hreg : Set.Iio 0 ⊆ X.D.regular)
    {D : RealTimeInterval} (a : ℝ) (hD : D.carrier ⊆ Set.Ioi a) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    MetricFamilySmoothOn (I := I) D (fun t => co.gInf (a - t)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  apply metricFamilySmoothOn_of_contMDiffOn
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × P.M => (a - p.1, p.2)) :=
    (contMDiff_const.sub contMDiff_fst).prodMk contMDiff_snd
  have hmaps : Set.MapsTo (fun p : ℝ × P.M => (a - p.1, p.2))
      (D.carrier ×ˢ Set.univ) (Set.Iio 0 ×ˢ Set.univ) := by
    intro p hp
    change a - p.1 < 0 ∧ p.2 ∈ Set.univ
    exact ⟨sub_neg.mpr (hD hp.1), hp.2⟩
  exact (co.metricCLMSection_smooth (Φ := Φ) hreg).comp hmap.contMDiffOn hmaps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_smooth_time_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_smooth_time_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_smooth_time_sub ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.metric_smooth_time_sub

end DifferentialGeometry.CheegerGromovCompactness
