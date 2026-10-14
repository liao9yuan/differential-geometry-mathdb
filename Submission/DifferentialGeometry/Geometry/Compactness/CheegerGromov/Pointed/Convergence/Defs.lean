import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricSource

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section MetricCompactnessCore

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

def metricSourceConvergesOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (D : forall k : Nat, MetricSourceData (I := I) Φ k)
    (K : Set L.M)
    (p : Nat) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\ (D k).derivNormSupOn (I := I) K p < ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.metricSourceConvergesOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.metricSourceConvergesOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.metricSourceConvergesOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.metricSourceConvergesOn

structure MetricConvergenceData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) where
  domain : forall k : Nat, MetricSourceData (I := I) Φ k
  converges :
    forall K : Set L.M,
      (letI : TopologicalSpace L.M := L.topology; IsCompact K) →
      forall p : Nat, metricSourceConvergesOn (I := I) Φ domain K p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData

namespace MetricConvergenceData

def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (Cd : MetricConvergenceData (I := I) Φ) :
    MetricConvergenceData (I := I) (Φ.unrepoint b hbase) where
  domain k := (Cd.domain k).unrepoint b hbase k
  converges := by
    intro K hK p ε hε
    simpa only [PointedRiemannianConvergenceMaps.unrepoint_source,
      MetricSourceData.unrepoint_deriv_norm_sup_on] using Cd.converges K hK p ε hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.unrepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.unrepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.unrepoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.unrepoint

noncomputable def ofDerivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    {D : forall k : Nat, MetricSourceData (I := I) Φ k}
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p < ε) :
    MetricConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p ε hε
    obtain ⟨kSource, hSource⟩ := Φ.source_subset hK
    obtain ⟨kConvergence, hConvergence⟩ := hconv K hK p ε hε
    refine ⟨max kSource kConvergence, fun k hk => ?_⟩
    refine ⟨hSource k (le_trans (Nat.le_max_left kSource kConvergence) hk), ?_⟩
    exact hConvergence k (le_trans (Nat.le_max_right kSource kConvergence) hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofDerivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofDerivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofDerivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofDerivNormSupOn

noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (hσsource : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((MetricSourceData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsource k)
              (referenceMetric k)).derivNormSupOn (I := I) K p) < ε) :
    MetricConvergenceData (I := I) Φ :=
  MetricConvergenceData.ofDerivNormSupOn (I := I)
    (D := fun k => MetricSourceData.ofRestrictPullback (I := I)
      (Φ := Φ) (k := k) (hσsource k) (referenceMetric k))
    hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofRestrictPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofRestrictPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofRestrictPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofRestrictPullback

end MetricConvergenceData

structure PointedRiemannianConverges
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (L : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq) where
  metrics : MetricConvergenceData (I := I) Φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges

namespace PointedRiemannianConverges

def unrepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : forall i : Nat, (X.obj i).M)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.repoint b) L subseq}
    (hbase : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : TopologicalSpace (X.obj (subseq k)).M :=
        (X.obj (subseq k)).topology
      letI : ChartedSpace H (X.obj (subseq k)).M :=
        (X.obj (subseq k)).charted
      Φ.partialDiffeomorph k L.basepoint = (X.obj (subseq k)).basepoint)
    (C : PointedRiemannianConverges (I := I) (X.repoint b) L subseq Φ) :
    PointedRiemannianConverges (I := I) X L subseq (Φ.unrepoint b hbase) where
  metrics := C.metrics.unrepoint b hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.unrepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.unrepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.unrepoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.unrepoint

noncomputable def ofDerivNormSupOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    {D : forall k : Nat, MetricSourceData (I := I) Φ k}
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p < ε) :
    PointedRiemannianConverges (I := I) X L subseq Φ where
  metrics := MetricConvergenceData.ofDerivNormSupOn (I := I) hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofDerivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofDerivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofDerivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofDerivNormSupOn

noncomputable def ofRestrictPullback
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hσsource : forall k : Nat,
      letI : TopologicalSpace L.M := L.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainTopology (I := I) Φ k
      letI : ChartedSpace H (MetricSourceDomain (I := I) Φ k) :=
        metricSourceDomainChartedSpace (I := I) Φ k
      letI : IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) :=
        metric_source_domain_smooth (I := I) Φ k
      SmoothRiemannianMetric I (MetricSourceDomain (I := I) Φ k))
    (hconv : forall K : Set L.M,
      forall _hK : letI : TopologicalSpace L.M := L.topology; IsCompact K,
      forall p : Nat,
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((MetricSourceData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsource k)
              (referenceMetric k)).derivNormSupOn (I := I) K p) < ε) :
    PointedRiemannianConverges (I := I) X L subseq Φ where
  metrics := MetricConvergenceData.ofRestrictPullback (I := I)
    hσsource referenceMetric hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofRestrictPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofRestrictPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofRestrictPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofRestrictPullback

end PointedRiemannianConverges

structure MetricCompactLimit
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  subseq : Nat -> Nat
  strictMono : StrictMono subseq
  limit : PointedRiemannianManifold.{u, uE, uH} (I := I)
  limit_complete : MetricComplete (I := I) limit
  maps : PointedRiemannianConvergenceMaps (I := I) X limit subseq
  convergence : PointedRiemannianConverges (I := I) X limit subseq maps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit

end MetricCompactnessCore

end CheegerGromovCompactness
end DifferentialGeometry
