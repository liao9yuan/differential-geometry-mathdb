import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Subsequence

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.SmoothCheegerGromovLimit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

def pointedCGHMapsOfAtZero
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat)
    (rmaps : PointedRiemannianConvergenceMaps (I := I) (X.atZero (I := I))
      (L.atTime (I := I) 0) subseq) :
    PointedCGHMaps (I := I) X (L.atTime 0) subseq where
  partialDiffeomorph := rmaps.partialDiffeomorph
  source_exhausts := rmaps.source_exhausts
  base_mem := rmaps.base_mem
  basepoint_map := rmaps.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfAtZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfAtZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfAtZero ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfAtZero

def pointedCGHMapsOfManifold
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (rmaps : PointedRiemannianConvergenceMaps (I := I) (X.atZero (I := I)) P subseq) :
    PointedCGHMaps (I := I) X P subseq where
  partialDiffeomorph := rmaps.partialDiffeomorph
  source_exhausts := rmaps.source_exhausts
  base_mem := rmaps.base_mem
  basepoint_map := rmaps.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfManifold ``Submission.DifferentialGeometry.CheegerGromovCompactness.pointedCGHMapsOfManifold

def cghMapsOfHL0
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactLimit (I := I) (X.atZero (I := I)))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit) :
    PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq :=
  pointedCGHMapsOfAtZero (I := I) X L mc.subseq (hL0.symm ▸ mc.maps)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.cghMapsOfHL0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.cghMapsOfHL0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.cghMapsOfHL0 ``Submission.DifferentialGeometry.CheegerGromovCompactness.cghMapsOfHL0

structure SmoothFlowLimitAlongMetricSubsequence
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactLimit (I := I) (X.atZero (I := I))) where
  L : PointedFlowData.{u, uE, uH} (I := I) X.D
  atTime_zero : L.atTime (I := I) 0 = mc.limit
  maps : PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq
  metric : MetricPullbackTendsto (I := I) maps
  scalar : ScalarPullbackTendsto (I := I) maps
  ricci : RicciPullbackTendsto (I := I) maps
  ricciNorm : RicNormPullback (I := I) maps

  source_sigmaCompact : forall k : Nat,
    letI : TopologicalSpace (L.atTime 0).M := L.topology
    IsSigmaCompact (maps.source k)
  target_sigmaCompact : forall k : Nat,
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    IsSigmaCompact (maps.target k)
  refMetric : forall k : Nat,
    letI : TopologicalSpace (SourceDomain (I := I) maps k) := sourceDomTop (I := I) maps k
    letI : ChartedSpace H (SourceDomain (I := I) maps k) := sourceDomCharted (I := I) maps k
    letI : IsManifold I ∞ (SourceDomain (I := I) maps k) := sourceDomSmooth (I := I) maps k
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) maps k)

  convergence : forall K : Set (L.atTime 0).M,
    forall _hK : letI : TopologicalSpace (L.atTime 0).M := L.topology; IsCompact K,
    forall p : Nat,
    forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t : Real, t ∈ Set.Icc a b ->
            ((SourceDomainMetricData.ofRestrictPullback (I := I)
              (Φ := maps) (k := k) (source_sigmaCompact k)
              (refMetric k) (letI : TopologicalSpace L.M := L.topology; letI : ChartedSpace H L.M :=
                                                                          L.charted; letI : IsManifold I ∞ L.M := L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := (by change IsManifold I ∞ L.M; infer_instance); letI : SigmaCompactSpace L.M := L.sigmaCompact; letI : T2Space L.M := L.t2; L.S.family.metric)).derivNormSupOn (I := I) K p t) < ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence

namespace SmoothFlowLimitAlongMetricSubsequence

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasSmoothCheegerGromovLimit
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactLimit (I := I) (X.atZero (I := I)))
    (d : SmoothFlowLimitAlongMetricSubsequence (I := I) X mc) :
    HasSmoothCheegerGromovLimit (I := I) X :=
  ⟨d.L, mc.subseq, mc.strictMono,
    ⟨SmoothCGHConverges.ofRestrictPullback (I := I)
      d.maps d.metric d.scalar d.ricci d.ricciNorm d.source_sigmaCompact d.refMetric
      (letI : TopologicalSpace d.L.M := d.L.topology
       letI : ChartedSpace H d.L.M := d.L.charted
       letI : IsManifold I ∞ d.L.M := d.L.smooth
       letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) d.L.M := by
         change IsManifold I ∞ d.L.M
         infer_instance
       letI : SigmaCompactSpace d.L.M := d.L.sigmaCompact
       letI : T2Space d.L.M := d.L.t2
       d.L.S.family.metric) d.convergence⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence.hasSmoothCheegerGromovLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence.hasSmoothCheegerGromovLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence.hasSmoothCheegerGromovLimit ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitAlongMetricSubsequence.hasSmoothCheegerGromovLimit

end SmoothFlowLimitAlongMetricSubsequence

structure SmoothFlowLimitSubsequence
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactLimit (I := I) (X.atZero (I := I))) where
  φ : Nat -> Nat
  strictMono : StrictMono φ
  limit : SmoothFlowLimitAlongMetricSubsequence (I := I) X (mc.compSubseq φ strictMono)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence

namespace SmoothFlowLimitSubsequence

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem hasSmoothCheegerGromovLimit
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {mc : MetricCompactLimit (I := I) (X.atZero (I := I))}
    (d : SmoothFlowLimitSubsequence (I := I) X mc) :
    HasSmoothCheegerGromovLimit (I := I) X :=
  SmoothFlowLimitAlongMetricSubsequence.hasSmoothCheegerGromovLimit
    (I := I) X (mc.compSubseq d.φ d.strictMono) d.limit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence.hasSmoothCheegerGromovLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence.hasSmoothCheegerGromovLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence.hasSmoothCheegerGromovLimit ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothFlowLimitSubsequence.hasSmoothCheegerGromovLimit

end SmoothFlowLimitSubsequence

end CheegerGromovCompactness
end DifferentialGeometry
