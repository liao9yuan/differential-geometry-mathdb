import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineMetricEquation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Equations.VolumeDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]



namespace CheegerGromovCompactness.HalfLineMetricConvergenceData

variable {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} (Φ : PointedCGHMaps X P subseq)

variable {R : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    SmoothRiemannianMetric I P.M}
  {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
  (co : HalfLineMetricConvergenceData Φ R bf hsrc htgt)

theorem contDiffOn_chartDensity
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular) (α : P.M) {x : P.M}
    (hx : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ContDiffOn ℝ ∞ (fun s => chartDensity (I := I) (co.gInf s) α x) (_root_.Set.Iio 0) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  have hc := chartDensity_family_contMDiffOn co.gInf α (gramSmooth Φ co hreg α)
  exact (hc.comp (contMDiffOn_id.prodMk contMDiffOn_const)
    (fun s hs => ⟨hs, hx⟩)).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.contDiffOn_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.contDiffOn_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.contDiffOn_chartDensity ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.contDiffOn_chartDensity

theorem hasDerivAt_chartDensity
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular)
    {t : ℝ} (ht : t < 0) (α : P.M) {x : P.M}
    (hx : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    HasDerivAt (fun s => chartDensity (I := I) (co.gInf s) α x)
      (-metricScalarAt (co.gInf t) x * chartDensity (co.gInf t) α x) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  have hd := Integral.Measure.hasDerivAt_chartDensity_of_chartGram_contMDiffOn
    isOpen_Iio (gramSmooth Φ co hreg) ht α hx
  have htrace := PDE.RicciFlow.traceTimeDerivMetric_eq_neg_two_scalar_of_ricciFlow
    co.gInf (metric_hasDerivAt Φ co hreg ht) x
  rw [htrace] at hd
  exact hd.congr_deriv (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity

theorem hasDerivAt_chartDensity_time_sub
    (hreg : _root_.Set.Iio 0 ⊆ X.D.regular)
    {a t : ℝ} (ht : a < t) (α : P.M) {x : P.M}
    (hx : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    HasDerivAt (fun s => chartDensity (I := I) (co.gInf (a - s)) α x)
      (metricScalarAt (co.gInf (a - t)) x * chartDensity (co.gInf (a - t)) α x) t := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  have hd := (hasDerivAt_chartDensity Φ co hreg (sub_neg.mpr ht) α hx).comp t
    ((hasDerivAt_const t a).sub (hasDerivAt_id t))
  exact hd.congr_deriv (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity_time_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity_time_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity_time_sub ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.hasDerivAt_chartDensity_time_sub

end CheegerGromovCompactness.HalfLineMetricConvergenceData

end DifferentialGeometry
