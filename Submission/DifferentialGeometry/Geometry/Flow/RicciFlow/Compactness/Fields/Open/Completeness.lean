import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.MetricLowerBound

import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Completeness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace OpenMetricConvergenceData

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
theorem complete_at
    (hP : MetricComplete (I := I) P)
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b t₀ : Real}
    (co : OpenMetricConvergenceData (I := I) Φ P.metric bf hsrc htgt a b t₀)
    (c : Nat → Real) (hc : ∀ n, 0 < c n)
    (hseq : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      ∀ (n k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n →
          ∀ (x : P.M) (v : TangentSpace I x),
            c n * P.metric.inner x v v ≤
              (gSeqExt (I := I) Φ P.metric bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ Set.Ioo a b) :
    MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  obtain ⟨c₀, hc₀, hlower⟩ := metric_lower Φ co c hc hseq ht
  exact MetricComplete.complete_of_lower P hP (co.gInf t) c₀ hc₀ hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.complete_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.complete_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.complete_at ``Submission.DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.complete_at

end OpenMetricConvergenceData
end CheegerGromovCompactness
end DifferentialGeometry

end
