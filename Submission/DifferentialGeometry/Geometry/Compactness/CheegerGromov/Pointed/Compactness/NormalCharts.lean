import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.BoundedGeometry

import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace MetricCompactSeed

def higherRegularityCanonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    CanonicalMetricCompactness (I := I) X := by
  let P : ∀ j : Nat, ProperMetricOn (I := I) (X.obj j) :=
    fun j => properMetricOn (I := I) (X.obj j)
      (hcomplete.complete j) (hconn j)
  let hraw := b.exists_pairwise_approximate_isometry_subsequence_of_bounded_geometry d hcomplete hconn
  let psi : Nat → Nat := Classical.choose hraw
  have hraw_spec := Classical.choose_spec hraw
  have hpsi : StrictMono psi := hraw_spec.1
  have B := hraw_spec.2
  let Ppsi : ∀ k : Nat, ProperMetricOn (I := I) ((X.subseq psi).obj k) :=
    fun k => P (psi k)
  let canon : CanonicalMetricCompactness (I := I) (X.subseq psi) :=
    canonicalMetricCompactness Ppsi B
  exact canon.ofSubsequence psi hpsi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityCanonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityCanonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityCanonicalMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityCanonicalMetricCompactness

def higherRegularityMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactLimit (I := I) X :=
  (b.higherRegularityCanonicalMetricCompactness d hcomplete hconn).compactness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higherRegularityMetricCompactness

theorem higher_regularity_canonical_metric_compactness_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactSeed (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := b.higherRegularityCanonicalMetricCompactness d hcomplete hconn
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ConnectedSpace C.compactness.limit.M := by
  classical
  dsimp only [higherRegularityCanonicalMetricCompactness, CanonicalMetricCompactness.ofSubsequence,
    MetricCompactLimit.ofSeqSubseq]
  exact canonical_metric_compactness_connected (I := I) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higher_regularity_canonical_metric_compactness_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higher_regularity_canonical_metric_compactness_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higher_regularity_canonical_metric_compactness_connected ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactSeed.higher_regularity_canonical_metric_compactness_connected

end MetricCompactSeed

namespace MetricCompactBase

def higherRegularityCanonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    CanonicalMetricCompactness (I := I) X :=
  b.toSeed.higherRegularityCanonicalMetricCompactness d hcomplete hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityCanonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityCanonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityCanonicalMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityCanonicalMetricCompactness

def higherRegularityMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactLimit (I := I) X :=
  b.toSeed.higherRegularityMetricCompactness d hcomplete hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higherRegularityMetricCompactness

theorem higher_regularity_canonical_metric_compactness_connected
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (b : MetricCompactBase (I := I) X)
    (d : BoundedGeometryNormalChartData (I := I) X b.decay)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    let C := b.higherRegularityCanonicalMetricCompactness d hcomplete hconn
    letI : TopologicalSpace C.compactness.limit.M := C.compactness.limit.topology
    ConnectedSpace C.compactness.limit.M := by
  change @ConnectedSpace
    (b.toSeed.higherRegularityCanonicalMetricCompactness d hcomplete hconn).compactness.limit.M
    (b.toSeed.higherRegularityCanonicalMetricCompactness d hcomplete hconn).compactness.limit.topology
  exact
    b.toSeed.higher_regularity_canonical_metric_compactness_connected d hcomplete hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higher_regularity_canonical_metric_compactness_connected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higher_regularity_canonical_metric_compactness_connected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higher_regularity_canonical_metric_compactness_connected ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactBase.higher_regularity_canonical_metric_compactness_connected

end MetricCompactBase
end CheegerGromovCompactness
end DifferentialGeometry
