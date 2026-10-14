import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.BoundedGeometry


import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

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

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace MetricCompactnessAssumptions

def canonicalMetricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    CanonicalMetricCompactness (I := I) X := by
  let P : forall j : Nat, ProperMetricOn (I := I) (X.obj j) :=
    fun j => properMetricOn (I := I) (X.obj j)
      (hcomplete.complete j) (hconn j)
  let hraw := inp.toBase.exists_pairwise_approximate_isometry_subsequence hcomplete hconn
  let psi : Nat → Nat := Classical.choose hraw
  have hraw_spec := Classical.choose_spec hraw
  have hpsi : StrictMono psi := hraw_spec.1
  have B := hraw_spec.2
  let Ppsi : forall k : Nat, ProperMetricOn (I := I) ((X.subseq psi).obj k) :=
    fun k => P (psi k)
  let canon : CanonicalMetricCompactness (I := I) (X.subseq psi) :=
    CheegerGromovCompactness.canonicalMetricCompactness Ppsi B
  exact canon.ofSubsequence psi hpsi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.canonicalMetricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.canonicalMetricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.canonicalMetricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.canonicalMetricCompactness

def metricCompactness
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : forall k : Nat,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M) :
    MetricCompactLimit (I := I) X :=
  (canonicalMetricCompactness inp hcomplete hconn).compactness

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.metricCompactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.metricCompactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.metricCompactness ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactnessAssumptions.metricCompactness

end MetricCompactnessAssumptions
end CheegerGromovCompactness
end DifferentialGeometry
