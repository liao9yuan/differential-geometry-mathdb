import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm

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

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.Bundle _root_.Submission.Bundle

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

structure PointedFlowData
    (I : ModelWithCorners Real E H)
      (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) where
  M : Type u
  [topology : TopologicalSpace M]
  [charted : ChartedSpace H M]
  [smooth : IsManifold I ∞ M]
  [sigmaCompact : SigmaCompactSpace M]
  [t2 : T2Space M]
  [t2TangentBundle : T2Space (TangentBundle I M)]
  basepoint : M
  S :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D
  isSolution :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
      change IsManifold I ∞ M
      infer_instance
    DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData

namespace PointedFlowData

variable {I : ModelWithCorners Real E H}
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def atTime (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : Real) :
    PointedRiemannianManifold.{u, uE, uH} (I := I) where
  M := F.M
  topology := F.topology
  charted := F.charted
  smooth := F.smooth
  sigmaCompact := F.sigmaCompact
  t2 := F.t2
  t2TangentBundle := F.t2TangentBundle
  basepoint := F.basepoint
  metric := by
    letI : TopologicalSpace F.M := F.topology
    letI : ChartedSpace H F.M := F.charted
    letI : IsManifold I ∞ F.M := F.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
      change IsManifold I ∞ F.M
      infer_instance
    letI : SigmaCompactSpace F.M := F.sigmaCompact
    letI : T2Space F.M := F.t2
    exact F.S.family.metric t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.atTime ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.atTime

def rmNormSq (F : PointedFlowData (I := I) D) (t : Real) (x : F.M) : Real :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  Tensor0SBundle.normSq0S (I := I) (F.S.family.metric t) x 4
    (F.S.base.rm04 t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.rmNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.rmNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.rmNormSq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.rmNormSq

end PointedFlowData

structure PointedFlowSeq (I : ModelWithCorners Real E H) where
  D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval
  term : Nat -> PointedFlowData.{u, uE, uH} (I := I) D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq

namespace PointedFlowSeq

variable {I : ModelWithCorners Real E H}

def basepoint (X : PointedFlowSeq.{u, uE, uH} (I := I)) (i : Nat) :
    (X.term i).M :=
  (X.term i).basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.basepoint ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.basepoint

def atTime (X : PointedFlowSeq.{u, uE, uH} (I := I)) (t : Real) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) where
  obj := fun i => (X.term i).atTime (I := I) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atTime ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atTime

def atZero (X : PointedFlowSeq.{u, uE, uH} (I := I)) :
    PointedRiemannianSeq.{u, uE, uH} (I := I) :=
  X.atTime (I := I) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atZero ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.atZero

end PointedFlowSeq

structure FlowMetricComplete {I : ModelWithCorners Real E H}
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  complete_on :
    forall i : Nat, forall t : Real, t ∈ X.D.carrier ->
      MetricComplete (I := I) ((X.term i).atTime (I := I) t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete

namespace FlowMetricComplete

theorem at_time {I : ModelWithCorners Real E H}
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (h : FlowMetricComplete (I := I) X) {t : Real} (ht : t ∈ X.D.carrier) :
    SeqMetricComplete (I := I) (X.atTime (I := I) t) where
  complete := fun i => h.complete_on i t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete.at_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete.at_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete.at_time ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowMetricComplete.at_time

end FlowMetricComplete

structure FlowCurvatureBoundedOnCompactWindows {I : ModelWithCorners Real E H}
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) : Prop where
  bound_on_window :
    forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      exists C : Real, 0 <= C /\
        forall i : Nat, forall t : Real, t ∈ Set.Icc a b ->
          forall x : (X.term i).M,
            (X.term i).rmNormSq (I := I) t x <= C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FlowCurvatureBoundedOnCompactWindows then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FlowCurvatureBoundedOnCompactWindows"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FlowCurvatureBoundedOnCompactWindows ``Submission.DifferentialGeometry.CheegerGromovCompactness.FlowCurvatureBoundedOnCompactWindows

end CheegerGromovCompactness
end DifferentialGeometry
