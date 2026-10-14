import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]

theorem exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : forall i : Nat,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hsub : HasSubsequencePairwiseApproximateIsometries (I := I) X
      (fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconnected k))) :
    exists P : MetricCompactLimit (I := I) X,
      (forall k : Nat, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (forall k : Nat,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M ∧
       (∀ n, IsCompact (closure (P.maps.source n))) ∧
       (∀ n, IsConnected (P.maps.source n)) ∧
       ∀ n, closure (P.maps.source n) ⊆ P.maps.source (n + 1)) := by
  obtain ⟨C⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) X hcomplete hconnected hsub
  exact ⟨C.canonical.compactness, C.canonical.domain_eq_canonical,
    C.canonical.reference_eq_limit, C.connected,
    C.source_precompact, C.source_connected, C.source_closure_subset⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries

theorem exists_canonicalMetricCompactLimit_of_hasSubsequencePairwiseApproximateIsometries
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : forall i : Nat,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hsub : HasSubsequencePairwiseApproximateIsometries (I := I) X
      (fun k => properMetricOn (I := I) (X.obj k) (hcomplete.complete k) (hconnected k))) :
    exists P : MetricCompactLimit (I := I) X,
      (forall k : Nat, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (forall k : Nat,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨P, hdomain, hreference, hconnected, _hprecompact, _hsourceConnected, _hnested⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_hasSubsequencePairwiseApproximateIsometries
      X hcomplete hconnected hsub
  exact ⟨P, hdomain, hreference, hconnected⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_canonicalMetricCompactLimit_of_hasSubsequencePairwiseApproximateIsometries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_canonicalMetricCompactLimit_of_hasSubsequencePairwiseApproximateIsometries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_canonicalMetricCompactLimit_of_hasSubsequencePairwiseApproximateIsometries ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_canonicalMetricCompactLimit_of_hasSubsequencePairwiseApproximateIsometries

end CheegerGromovCompactness
end DifferentialGeometry

end
