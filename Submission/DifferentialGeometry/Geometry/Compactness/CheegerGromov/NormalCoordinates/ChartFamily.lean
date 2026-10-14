import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Basic
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import Submission.DifferentialGeometry.Geometry.Comparison.NormalCoordinates.Smoothness
import Submission.DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

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

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Bundle _root_.Submission.Bundle

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section ControlledNormalCharts

variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

abbrev NormalChartAt
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) : Type (max u uE) :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  NormalBallChart (I := I) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartAt ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartAt

abbrev NormalChartFamily
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :=
  ∀ (k : Nat) (x : (X.obj k).M),
    NormalChartAt (I := I) (X.obj k) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily

namespace NormalChartFamily

def radius
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x : (X.obj k).M) : Real :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).radius

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.radius ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.radius

def hom
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x : (X.obj k).M) : E → (X.obj k).M :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.hom ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.hom

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (f : Nat → Nat) :
    NormalChartFamily (I := I) (X.subseq f) :=
  fun k x => chart (f k) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.subseq

def transition
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x y : (X.obj k).M) : E → E :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).transition (chart k y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.transition ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.transition

noncomputable def metric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X) (k : Nat)
    (x : (X.obj k).M) : E → (E →L[Real] E →L[Real] Real) :=
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  (chart k x).metric (X.obj k).metric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalChartFamily.metric

end NormalChartFamily

noncomputable def c2RadiusNormalBallChart
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    NormalBallChart (I := I) x := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let U := Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x)
  have hsub : U ⊆ (expMapDiffeo (I := I) Y.metric x).source := by
    intro z hz
    apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Y.metric x
    simpa only [U, Metric.mem_ball, dist_zero_right] using hz
  have himage :
      (fun z => expMapDiffeo (I := I) Y.metric x z) '' U =
        (fun z : E => (expMap (I := I) Y.metric x
          (show TangentSpace I x from z) : Y.M)) '' U := by
    apply Set.image_congr
    intro z hz
    exact expMapDiffeo_apply_eq (I := I) Y.metric x (hsub hz)
  exact
    { radius := expMapC2Radius (I := I) Y.metric x
      radius_pos := expMapC2Radius_pos (I := I) Y.metric x
      hom := expMapDiffeo (I := I) Y.metric x
      ball_subset := hsub
      map_zero := expMapDiffeo_zero (I := I) Y.metric x
      smooth_to := exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) Y x
      smooth_inv := by
        rw [himage]
        exact normal_chart_at_cont_mdiff_on_infty (I := I) Y.metric x }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalBallChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalBallChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalBallChart ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalBallChart

noncomputable def c2RadiusNormalChartFamily
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) :
    NormalChartFamily (I := I) X :=
  fun k x => c2RadiusNormalBallChart (I := I) (X.obj k) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalChartFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalChartFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalChartFamily ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2RadiusNormalChartFamily

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_radius
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).radius =
      expMapC2Radius (I := I) Y.metric x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_radius ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_radius

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_apply
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (z : E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).hom z =
      expMapDiffeo (I := I) Y.metric x z := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_apply ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_apply

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_inv
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).inv =
      normalChartAt (I := I) Y.metric x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_inv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_inv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_inv ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_inv

omit [NeZero (Module.finrank Real E)] in
@[simp] theorem c2_radius_normal_ball_chart_target
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).hom.target =
      (normalChartAt (I := I) Y.metric x).source := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_target ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_target

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_image
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).hom ''
        Metric.ball (0 : E) (c2RadiusNormalBallChart (I := I) Y x).radius =
      (fun z : E => (expMap (I := I) Y.metric x (show TangentSpace I x from z) : Y.M)) ''
        Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [c2_radius_normal_ball_chart_radius]
  apply Set.image_congr
  intro z hz
  rw [c2_radius_normal_ball_chart_apply]
  exact expMapDiffeo_apply_eq (I := I) Y.metric x
    ((c2RadiusNormalBallChart (I := I) Y x).ball_subset hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_image ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_image

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_metric
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).metric Y.metric =
    normalCoordMetric (I := I) Y x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric

def NormalCoordMetricBounds.metricBounds
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (c2RadiusNormalBallChart (I := I) (X.obj k) x).MetricBounds
      (X.obj k).metric := by
  letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
  letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
  letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  letI : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  exact
    { C := h.metricC
      C_nonneg := h.metricC_nonneg
      radius := h.radius k x
      radius_pos := h.radius_pos k x
      equiv := by
        simpa only [NormalBallChart.MetricEquivOn, NormalCoordMetricEquivOn,
          c2_radius_normal_ball_chart_metric] using
          h.metric_equiv k x
      deriv := fun p => by
        simpa only [NormalBallChart.MetricDerivBound, NormalCoordMetricDerivBound,
          c2_radius_normal_ball_chart_metric] using
          h.metric_deriv k p x }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.NormalCoordMetricBounds.metricBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.NormalCoordMetricBounds.metricBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.NormalCoordMetricBounds.metricBounds ``Submission.DifferentialGeometry.CheegerGromovCompactness.NormalCoordMetricBounds.metricBounds

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_transition
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).transition
        (c2RadiusNormalBallChart (I := I) Y y) =
      normalTransition (I := I) Y x y := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_transition ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_transition

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_overlap_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x y : Y.M) (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).OverlapOn
        (c2RadiusNormalBallChart (I := I) Y y) U ↔
      ∀ z ∈ U,
        z ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric x) ∧
        expMapDiffeo (I := I) Y.metric x z ∈
          (fun z : E => (expMap (I := I) Y.metric y (show TangentSpace I y from z) : Y.M)) ''
            Metric.ball (0 : E) (expMapC2Radius (I := I) Y.metric y) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [NormalBallChart.OverlapOn, c2_radius_normal_ball_chart_radius,
    c2_radius_normal_ball_chart_image]
  simp only [c2_radius_normal_ball_chart_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_overlap_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_overlap_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_overlap_iff ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_overlap_iff

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_metric_equiv_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (U : Set E) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).MetricEquivOn Y.metric U ↔
      NormalCoordMetricEquivOn (I := I) Y x U := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [NormalBallChart.MetricEquivOn, NormalCoordMetricEquivOn,
    c2_radius_normal_ball_chart_metric (I := I)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_equiv_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_equiv_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_equiv_iff ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_equiv_iff

omit [NeZero (Module.finrank Real E)] in
theorem c2_radius_normal_ball_chart_metric_deriv_iff
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (x : Y.M) (U : Set E) (p : Nat) (C : Real) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    (c2RadiusNormalBallChart (I := I) Y x).MetricDerivBound
        Y.metric U p C ↔
      NormalCoordMetricDerivBound (I := I) Y x U p C := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [NormalBallChart.MetricDerivBound, NormalCoordMetricDerivBound,
    c2_radius_normal_ball_chart_metric (I := I)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_deriv_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_deriv_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_deriv_iff ``Submission.DifferentialGeometry.CheegerGromovCompactness.c2_radius_normal_ball_chart_metric_deriv_iff

end ControlledNormalCharts

end CheegerGromovCompactness
end DifferentialGeometry
