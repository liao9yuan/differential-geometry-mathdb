import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Submission.DifferentialGeometry.Geometry.Metric.Basic

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

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]

structure PointedRiemannianManifold
    (I : ModelWithCorners Real E H) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2TangentBundle : T2Space (TangentBundle I M)]
  basepoint : M
  metric : SmoothRiemannianMetric I M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold

namespace PointedRiemannianManifold

variable {I : ModelWithCorners Real E H}

def repoint (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : X.M) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) :=
  { X with basepoint := x }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.repoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.repoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.repoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianManifold.repoint

end PointedRiemannianManifold

structure PointedRiemannianSeq (I : ModelWithCorners Real E H) where
  obj : Nat -> PointedRiemannianManifold.{u, uE, uH} (I := I)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq

namespace PointedRiemannianSeq

variable {I : ModelWithCorners Real E H}

abbrev Distance
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Type _ :=
  ∀ k : Nat, (X.obj k).M → (X.obj k).M → Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.Distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.Distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.Distance ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.Distance

def basepoint (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (i : Nat) :
    (X.obj i).M :=
  (X.obj i).basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.basepoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.basepoint

def subseq (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) (f : Nat -> Nat) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := fun i => X.obj (f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.subseq

def repoint (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (b : forall i : Nat, (X.obj i).M) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj i := (X.obj i).repoint (b i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.repoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.repoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.repoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.repoint

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem connected_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : ∀ k,
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (f : Nat → Nat) :
    ∀ k,
      letI : TopologicalSpace ((X.subseq f).obj k).M :=
        ((X.subseq f).obj k).topology
      ConnectedSpace ((X.subseq f).obj k).M := by
  intro k
  change @ConnectedSpace (X.obj (f k)).M (X.obj (f k)).topology
  exact hX (f k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connected_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connected_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connected_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianSeq.connected_subseq

end PointedRiemannianSeq

def MetricComplete {I : ModelWithCorners Real E H}
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : IsManifold I 1 X.M :=
    IsManifold.of_le (I := I) (M := X.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  letI : TopologicalSpace.MetrizableSpace X.M :=
    Manifold.metrizableSpace I X.M
  letI : T3Space X.M := inferInstance
  letI : _root_.Bundle.RiemannianBundle (fun x : X.M => TangentSpace I x) :=
    ⟨X.metric.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (fun x : X.M => TangentSpace I x) :=
    ⟨⟨X.metric.inner, X.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M
  CompleteSpace X.M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricComplete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricComplete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricComplete ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricComplete

namespace MetricComplete

omit [CompleteSpace E] in
theorem complete {I : ModelWithCorners Real E H}
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hX : MetricComplete (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : IsManifold I 1 X.M :=
      IsManifold.of_le (I := I) (M := X.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    letI : TopologicalSpace.MetrizableSpace X.M :=
      Manifold.metrizableSpace I X.M
    letI : T3Space X.M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun x : X.M => TangentSpace I x) :=
      ⟨X.metric.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : X.M => TangentSpace I x) :=
      ⟨⟨X.metric.inner, X.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace X.M := EMetricSpace.ofRiemannianMetric I X.M
    CompleteSpace X.M := by
  simpa [MetricComplete] using hX

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricComplete.complete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricComplete.complete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricComplete.complete ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricComplete.complete

end MetricComplete

structure SeqMetricComplete {I : ModelWithCorners Real E H}
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) : Prop where
  complete : forall i : Nat, MetricComplete (I := I) (X.obj i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete

namespace SeqMetricComplete

variable {I : ModelWithCorners Real E H}

omit [CompleteSpace E] in
theorem subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqMetricComplete (I := I) X) (f : Nat -> Nat) :
    SeqMetricComplete (I := I) (X.subseq f) where
  complete := by
    intro i
    simpa [PointedRiemannianSeq.subseq] using hX.complete (f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.SeqMetricComplete.subseq

end SeqMetricComplete

end CheegerGromovCompactness
end DifferentialGeometry
