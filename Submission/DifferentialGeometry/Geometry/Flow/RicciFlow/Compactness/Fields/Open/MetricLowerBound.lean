import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Convergence

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricLowerBound

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
  [FiniteDimensional Real E]
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
theorem metric_lower
    {R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    {a b t₀ : Real} (co : OpenMetricConvergenceData (I := I) Φ R bf hsrc htgt a b t₀)
    (c : Nat → Real) (hc : ∀ n, 0 < c n)
    (hseq : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      ∀ (n k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n →
          ∀ (x : P.M) (v : TangentSpace I x),
            c n * R.inner x v v ≤
              (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t).inner x v v)
    {t : Real} (ht : t ∈ Set.Ioo a b) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ∃ c₀ : Real, 0 < c₀ ∧
      ∀ (x : P.M) (v : TangentSpace I x),
        c₀ * R.inner x v v ≤ (co.gInf t).inner x v v := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨n, htn⟩ := RealTimeInterval.mem_openWindow (t₀ := t₀) ht
  refine ⟨c n, hc n, ?_⟩
  exact FlowMetricConvergenceData.lower_of (I := I) (Φ := Φ) (OpenMetricConvergenceData.atWindow Φ co n)
    (hseq n) t htn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.metric_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.metric_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.metric_lower ``Submission.DifferentialGeometry.CheegerGromovCompactness.OpenMetricConvergenceData.metric_lower

end OpenMetricConvergenceData
end CheegerGromovCompactness
end DifferentialGeometry
