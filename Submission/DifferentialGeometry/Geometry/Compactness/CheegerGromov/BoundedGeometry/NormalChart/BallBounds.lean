import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalChart.Defs

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

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Bundle _root_.Submission.Bundle

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

structure SeqBallNormalChartData
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hd : InjectivityRadiusDecay (I := I) X)
    extends NormalChartData (I := I) X hd where
  metricC : Nat -> Nat -> Real
  metricC_nonneg : forall n p : Nat, 0 <= metricC n p
  metric_equiv : forall (k : Nat) (x : (X.obj k).M),
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (chart k x).MetricEquivOn (X.obj k).metric
      (Metric.ball (0 : E) (chart k x).radius)
  metric_deriv : forall (n p j : Nat), n + p <= j ->
    letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
    letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
    letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
    letI : T2Space (TangentBundle I (X.obj j).M) :=
      (X.obj j).t2TangentBundle
    forall x : (X.obj j).M,
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (n : Real) ->
      (chart j x).MetricDerivBound (X.obj j).metric
        (Metric.ball (0 : E) (chart j x).radius) p (metricC n p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData

namespace SeqBallNormalChartData

def of_boundedGeometryNormalChartData
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : BoundedGeometryNormalChartData (I := I) X hd) :
    SeqBallNormalChartData (I := I) X hd where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  ratio_mu0_le := d.ratio_mu0_le
  chart := d.chart
  radius_eq := d.radius_eq
  hom_eq := d.hom_eq
  metricC := fun _ p => d.metricC p
  metricC_nonneg := fun _ p => d.metricC_nonneg p
  metric_equiv := by
    intro k x
    with_unfolding_all
      exact d.metric_equiv k x
  metric_deriv := by
    intro n p j _hnj x _hx
    with_unfolding_all
      exact d.metric_deriv j p x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.of_boundedGeometryNormalChartData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.of_boundedGeometryNormalChartData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.of_boundedGeometryNormalChartData ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.of_boundedGeometryNormalChartData

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd) (f : Nat -> Nat)
    (hf : forall j : Nat, j <= f j) :
    SeqBallNormalChartData (I := I) (X.subseq f) (hd.subseq f) where
  ratio := d.ratio
  ratio_pos := d.ratio_pos
  ratio_mu0_le := by
    simpa only [InjectivityRadiusDecay.mu, InjectivityRadiusDecay.subseq,
      BaseInjBound.subseq] using d.ratio_mu0_le
  chart := fun k x => d.chart (f k) x
  radius_eq := by
    intro k x
    simpa only [InjectivityRadiusDecay.mu, InjectivityRadiusDecay.subseq,
      BaseInjBound.subseq, PointedRiemannianSeq.subseq] using d.radius_eq (f k) x
  hom_eq := by
    intro k x hcomplete
    with_unfolding_all
      exact d.hom_eq (f k) x hcomplete
  metricC := d.metricC
  metricC_nonneg := d.metricC_nonneg
  metric_equiv := by
    intro k x
    with_unfolding_all
      exact d.metric_equiv (f k) x
  metric_deriv := by
    intro n p j hnj x hx
    with_unfolding_all
      exact d.metric_deriv n p (f j) (le_trans hnj (hf j)) x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.subseq

omit [CompleteSpace E] in
theorem metric_deriv_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    {n p j : Nat} (hnj : n + p <= j) {x : (X.obj j).M}
    (hx : letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
      letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
      riemannianEDistOf (I := I) (X.obj j).metric (X.obj j).basepoint x <=
        ENNReal.ofReal (n : Real)) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.chart j x).MetricDerivBound (X.obj j).metric
       (Metric.ball (0 : E) (d.chart j x).radius) p (d.metricC n p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  exact d.metric_deriv n p j hnj x hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_le ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_le

omit [CompleteSpace E] in
theorem metric_deriv_basepoint
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X}
    (d : SeqBallNormalChartData (I := I) X hd)
    {n p j : Nat} (hnj : n + p <= j) :
    (letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
     letI : ChartedSpace H (X.obj j).M := (X.obj j).charted
     letI : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
     letI : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
     (d.chart j (X.obj j).basepoint).MetricDerivBound (X.obj j).metric
       (Metric.ball (0 : E) (d.chart j (X.obj j).basepoint).radius) p (d.metricC n p)) := by
  let : TopologicalSpace (X.obj j).M := (X.obj j).topology
  let : ChartedSpace H (X.obj j).M := (X.obj j).charted
  let : IsManifold I ∞ (X.obj j).M := (X.obj j).smooth
  let : T2Space (TangentBundle I (X.obj j).M) := (X.obj j).t2TangentBundle
  refine d.metric_deriv n p j hnj _ ?_
  rw [riemannianEDistOf_self]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_basepoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqBallNormalChartData.metric_deriv_basepoint

end SeqBallNormalChartData

end CheegerGromovCompactness
end DifferentialGeometry
