import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalMetricCompactnessSeed
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.BoundedGeometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

def StaircaseMetricCompactSeedFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  SeqMetricComplete (I := I) Y →
  (∀ i : ℕ,
    let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  BaseInjBound (I := I) Y →
  Nonempty (SeqBallGeometry (I := I) Y) →
  ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∃ b : MetricCompactSeed (I := I) (Y.subseq ψ),
      Nonempty (BoundedGeometryNormalChartData (I := I) (Y.subseq ψ) b.decay)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseMetricCompactSeedFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseMetricCompactSeedFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseMetricCompactSeedFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseMetricCompactSeedFrontier

def StaircaseApproximateIsometryFrontier
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop :=
  (hcomplete : SeqMetricComplete (I := I) Y) →
  (hconnected : ∀ i : ℕ,
    let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
    ConnectedSpace (Y.obj i).M) →
  (_hinj : BaseInjBound (I := I) Y) →
  (_hball : Nonempty (SeqBallGeometry (I := I) Y)) →
  HasSubsequencePairwiseApproximateIsometries (I := I) Y
    (fun k => properMetricOn (I := I) (Y.obj k) (hcomplete.complete k) (hconnected k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseApproximateIsometryFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseApproximateIsometryFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseApproximateIsometryFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.StaircaseApproximateIsometryFrontier

theorem exists_local_pointed_metric_compactness_of_staircaseApproximateIsometryFrontier
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
      ConnectedSpace (X.obj i).M)
    (hinj : BaseInjBound (I := I) X)
    (hjets : ∀ A : ℝ, 0 < A → ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ i in _root_.Filter.atTop,
        let _ : TopologicalSpace (X.obj i).M := (X.obj i).topology
        let _ : ChartedSpace H (X.obj i).M := (X.obj i).charted
        let _ : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
        let _ : T2Space (X.obj i).M := (X.obj i).t2
        let _ : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
        ∀ x : (X.obj i).M,
          riemannianEDistOf (I := I) (X.obj i).metric (X.obj i).basepoint x ≤
            ENNReal.ofReal A → curvDerivNorm (I := I) p (X.obj i).metric x ≤ C)
    (hfrontier : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseApproximateIsometryFrontier (I := I) Y) :
    ∃ P : MetricCompactLimit (I := I) X,
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData (I := I) P.maps k) ∧
      (∀ k : ℕ,
        let D := P.convergence.metrics.domain k
        let _ : TopologicalSpace (MetricSourceDomain (I := I) P.maps k) := D.topology
        let _ : ChartedSpace H (MetricSourceDomain (I := I) P.maps k) := D.charted
        let _ : IsManifold I ∞ (MetricSourceDomain (I := I) P.maps k) := D.smooth
        D.referenceMetric = D.limitMetric) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨φ, hφ, hball⟩ := exists_subseq_seqBallGeometry_of_local_jets (I := I) X hjets
  obtain ⟨σ, hσ, hpair⟩ :=
    hfrontier (X.subseq φ) (hcomplete.subseq φ)
      (PointedRiemannianSeq.connected_subseq hconnected φ) (hinj.subseq φ) hball
  have hpairX : HasPairwiseApproximateIsometries (I := I) (X := X.subseq (φ ∘ σ))
      (fun k => properMetricOn (I := I) (X.obj ((φ ∘ σ) k))
        (hcomplete.complete ((φ ∘ σ) k)) (hconnected ((φ ∘ σ) k))) := hpair
  obtain ⟨C⟩ :=
    exists_connectedCanonicalMetricCompactness_of_hasSubsequencePairwiseApproximateIsometries
      (I := I) X hcomplete hconnected ⟨φ ∘ σ, hφ.comp hσ, hpairX⟩
  exact ⟨C.canonical.compactness, C.canonical.domain_eq_canonical,
    C.canonical.reference_eq_limit, C.connected⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_local_pointed_metric_compactness_of_staircaseApproximateIsometryFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_local_pointed_metric_compactness_of_staircaseApproximateIsometryFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_local_pointed_metric_compactness_of_staircaseApproximateIsometryFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_local_pointed_metric_compactness_of_staircaseApproximateIsometryFrontier

theorem staircaseApproximateIsometryFrontier_of_metricCompactSeedFrontier
    (hseed : ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseMetricCompactSeedFrontier (I := I) Y) :
    ∀ Y : PointedRiemannianSeq.{u, uE, uH} (I := I),
      StaircaseApproximateIsometryFrontier (I := I) Y := by
  intro Y hcomplete hconnected hinj hball
  obtain ⟨ψ, hψ, b, hd⟩ := hseed Y hcomplete hconnected hinj hball
  obtain ⟨psi, hpsi, hpair⟩ :=
    b.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry
      (Classical.choice hd) (hcomplete.subseq ψ)
      (PointedRiemannianSeq.connected_subseq hconnected ψ)
  exact ⟨ψ ∘ psi, hψ.comp hpsi, hpair⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staircaseApproximateIsometryFrontier_of_metricCompactSeedFrontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staircaseApproximateIsometryFrontier_of_metricCompactSeedFrontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staircaseApproximateIsometryFrontier_of_metricCompactSeedFrontier ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.staircaseApproximateIsometryFrontier_of_metricCompactSeedFrontier

theorem hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry
    (Y : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) Y)
    (hconnected : ∀ i : ℕ,
      let _ : TopologicalSpace (Y.obj i).M := (Y.obj i).topology
      ConnectedSpace (Y.obj i).M)
    (hgeom : SeqBoundedGeometry (I := I) Y)
    (hinj : BaseInjBound (I := I) Y) :
    HasSubsequencePairwiseApproximateIsometries (I := I) Y
      (fun k => properMetricOn (I := I) (Y.obj k) (hcomplete.complete k) (hconnected k)) := by
  let b : MetricCompactSeed (I := I) Y :=
    metricCompactSeedOfBoundedGeometry (I := I) Y hcomplete hgeom hinj hconnected
  have hd : Nonempty (BoundedGeometryNormalChartData (I := I) Y b.decay) :=
    nonempty_bounded_geometry_normal_chart_data (I := I) Y hcomplete hconnected hgeom
      b.decay b.realizes
  obtain ⟨psi, hpsi, hpair⟩ :=
    b.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry
      (Classical.choice hd) hcomplete hconnected
  exact ⟨psi, hpsi, hpair⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.hasSubsequencePairwiseApproximateIsometries_of_seqBoundedGeometry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
