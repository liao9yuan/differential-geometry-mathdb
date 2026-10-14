import Mathlib.Topology.MetricSpace.ProperSpace
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Ball
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Instances

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

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

structure ProperMetricOn {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  ms : MetricSpace Y.M
  realizes : ∀ x y : Y.M,
    (letI : EMetricSpace Y.M := Y.emetricSpace
     _root_.EDist.edist x y) =
    ENNReal.ofReal (letI : MetricSpace Y.M := ms
      _root_.Dist.dist x y)
  proper : letI : MetricSpace Y.M := ms
    ProperSpace Y.M
  exists_dist_to_basepoint_eq : letI : MetricSpace Y.M := ms
    ∀ p : Y.M, ∀ t : ℝ, 0 ≤ t → t ≤ _root_.Dist.dist p Y.basepoint →
      ∃ q : Y.M, _root_.Dist.dist q Y.basepoint = t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.top_eq {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = Y.topology := by
  have hem :
      (letI : MetricSpace Y.M := P.ms
       (inferInstance : PseudoEMetricSpace Y.M)) =
        (letI : EMetricSpace Y.M := Y.emetricSpace
         (inferInstance : PseudoEMetricSpace Y.M)) := by
    apply PseudoEMetricSpace.ext
    ext x y
    change (letI : MetricSpace Y.M := P.ms; _root_.EDist.edist x y) =
      (letI : EMetricSpace Y.M := Y.emetricSpace; _root_.EDist.edist x y)
    rw [P.realizes x y]
    have hdist :
        (letI : MetricSpace Y.M := P.ms
         _root_.EDist.edist x y) =
          ENNReal.ofReal (letI : MetricSpace Y.M := P.ms
            dist x y) := by
      let : MetricSpace Y.M := P.ms
      exact edist_dist x y
    exact hdist
  have htop :
      (letI : MetricSpace Y.M := P.ms
       (inferInstance : PseudoEMetricSpace Y.M).toUniformSpace.toTopologicalSpace) =
        (letI : EMetricSpace Y.M := Y.emetricSpace
         (inferInstance : PseudoEMetricSpace Y.M).toUniformSpace.toTopologicalSpace) := by
    simpa using
      congrArg (fun m : PseudoEMetricSpace Y.M => m.toUniformSpace.toTopologicalSpace) hem
  have hcan :
      (letI : EMetricSpace Y.M := Y.emetricSpace
       (inferInstance : PseudoEMetricSpace Y.M).toUniformSpace.toTopologicalSpace) =
        Y.topology := by
    rfl
  change P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = Y.topology
  rw [htop, hcan]

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.top_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.top_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.top_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.top_eq

namespace ProperMetricOn

@[reducible] noncomputable def alignedMetricSpace {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    MetricSpace Y.M := by
  letI : TopologicalSpace Y.M := Y.topology
  exact P.ms.replaceTopology (ProperMetricOn.top_eq Y P).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.alignedMetricSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.alignedMetricSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.alignedMetricSpace ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.alignedMetricSpace

end ProperMetricOn

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth in
omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.isCompact_riemannianClosedBallOf {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn Y) (x : Y.M) (r : ℝ) :
    IsCompact (riemannianClosedBallOf Y.metric x r) := by
  let : MetricSpace Y.M := P.alignedMetricSpace Y
  have heq : riemannianClosedBallOf Y.metric x r = Metric.closedBall x (_root_.Max.max 0 r) := by
    ext y
    change riemannianEDistOf Y.metric x y ≤ ENNReal.ofReal r ↔ _root_.Dist.dist y x ≤ _root_.Max.max 0 r
    have hreal := P.realizes x y
    change riemannianEDistOf Y.metric x y = ENNReal.ofReal (_root_.Dist.dist x y) at hreal
    rw [hreal, show ENNReal.ofReal r = ENNReal.ofReal (_root_.Max.max 0 r) by simp,
      ENNReal.ofReal_le_ofReal_iff (le_max_left 0 r), dist_comm]
  rw [heq]
  have hcompact : @IsCompact Y.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (letI : MetricSpace Y.M := P.ms; Metric.closedBall x (_root_.Max.max 0 r)) := by
    let : MetricSpace Y.M := P.ms
    let : ProperSpace Y.M := P.proper
    exact _root_.ProperSpace.isCompact_closedBall x (_root_.Max.max 0 r)
  rw [P.top_eq Y] at hcompact
  exact hcompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isCompact_riemannianClosedBallOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isCompact_riemannianClosedBallOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isCompact_riemannianClosedBallOf ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isCompact_riemannianClosedBallOf

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.isRiemannianManifold {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
    letI : MetricSpace Y.M := P.ms
    IsRiemannianManifold I Y.M := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) := Y.riemBundle
  let : MetricSpace Y.M := P.ms
  refine ⟨fun x y => ?_⟩
  have hreal := P.realizes x y
  rw [edist_dist, ← hreal]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isRiemannianManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isRiemannianManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isRiemannianManifold ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isRiemannianManifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem exists_proper_metric_on {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hc : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M) :
    Nonempty (ProperMetricOn (I := I) Y) := by
  classical
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Y.M := Y.smooth
  let : IsManifold I 1 Y.M :=
    IsManifold.of_le (I := I) (M := Y.M) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  let : SigmaCompactSpace Y.M := Y.sigmaCompact
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  have : TopologicalSpace.MetrizableSpace Y.M := Manifold.metrizableSpace I Y.M
  have : T3Space Y.M := inferInstance
  have : ConnectedSpace Y.M := hconn
  let rb : Bundle.RiemannianBundle (fun x : Y.M => TangentSpace I x) :=
    ⟨Y.metric.toRiemannianMetric⟩
  have hCont := Y.riemBundle_cont (I := I)
  have hcomplete :
      (letI : EMetricSpace Y.M := EMetricSpace.ofRiemannianMetric I Y.M
       CompleteSpace Y.M) := by
    simpa [MetricComplete] using hc
  let ms := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetricSpace
    (I := I) (M := Y.M)
  have hreal : ∀ x y : Y.M,
      (letI : EMetricSpace Y.M := Y.emetricSpace
       _root_.EDist.edist x y) =
      ENNReal.ofReal (letI : MetricSpace Y.M := ms
        dist x y) := by
    intro x y
    have h := DifferentialGeometry.Geometry.Riemannian.HopfRinow.riemMetric_realizes
      (I := I) (M := Y.M) x y
    simpa [PointedRiemannianManifold.emetricSpace, ms] using h
  have hproper :
      letI : MetricSpace Y.M := ms
      ProperSpace Y.M := by
    have h := DifferentialGeometry.Geometry.Riemannian.HopfRinow.properSpace_riemMetric
      (I := I) (M := Y.M) hcomplete Y.metric (by
        intro x v
        exact
          (DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle
            (I := I) Y.metric) x v)
    simpa [ms] using h
  have hhint :
      letI : MetricSpace Y.M := ms
      ∀ p : Y.M, ∀ t : ℝ, 0 ≤ t → t ≤ _root_.Dist.dist p Y.basepoint →
        ∃ q : Y.M, _root_.Dist.dist q Y.basepoint = t := by
    have h := DifferentialGeometry.Geometry.Riemannian.HopfRinow.intermediateDist_riemMetric
      (I := I) (M := Y.M) hcomplete Y.metric (by
        intro x v
        exact
          (DifferentialGeometry.Geometry.Riemannian.isMetricNorm_of_riemannianBundle
            (I := I) Y.metric) x v) Y.basepoint
    simpa [ms] using h
  exact ⟨⟨ms, hreal, hproper, hhint⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.exists_proper_metric_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.exists_proper_metric_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.exists_proper_metric_on ``Submission.DifferentialGeometry.CheegerGromovCompactness.exists_proper_metric_on

omit [CompleteSpace E] in
noncomputable def properMetricOn {I : ModelWithCorners Real E H}
    [I.Boundaryless]
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hc : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M) :
    ProperMetricOn (I := I) Y :=
  Classical.choice (exists_proper_metric_on (I := I) Y hc hconn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.properMetricOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.properMetricOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.properMetricOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.properMetricOn

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.isOpen_ball {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @IsOpen Y.M Y.topology
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  have hb :
      @IsOpen Y.M P.ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
        (letI : MetricSpace Y.M := P.ms
         Metric.ball x r) := by
    let : MetricSpace Y.M := P.ms
    exact Metric.isOpen_ball
  rw [P.top_eq Y] at hb
  exact hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isOpen_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isOpen_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isOpen_ball ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.isOpen_ball

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.mem_ball_self {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    x ∈
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) := by
  let : MetricSpace Y.M := P.ms
  exact Metric.mem_ball_self hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.mem_ball_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.mem_ball_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.mem_ball_self ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.mem_ball_self

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.ball_nonempty {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty
      (letI : MetricSpace Y.M := P.ms
       Metric.ball x r) :=
  ⟨⟨x, P.mem_ball_self Y x hr⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.ball_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.ball_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.ball_nonempty ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.ball_nonempty

def ProperMetricOn.openBall {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) (r : ℝ) :
    @TopologicalSpace.Opens Y.M Y.topology :=
  letI : TopologicalSpace Y.M := Y.topology
  ⟨(letI : MetricSpace Y.M := P.ms
    Metric.ball x r), P.isOpen_ball Y x r⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ProperMetricOn.openBall_nonempty {I : ModelWithCorners Real E H}
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) (x : Y.M) {r : ℝ} (hr : 0 < r) :
    Nonempty (P.openBall Y x r) := by
  let : TopologicalSpace Y.M := Y.topology
  exact P.ball_nonempty Y x hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall_nonempty ``Submission.DifferentialGeometry.CheegerGromovCompactness.ProperMetricOn.openBall_nonempty

end CheegerGromovCompactness
end DifferentialGeometry
