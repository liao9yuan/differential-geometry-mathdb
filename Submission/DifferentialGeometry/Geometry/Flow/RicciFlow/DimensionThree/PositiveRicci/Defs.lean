import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.RicciNorm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Regularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.Pinching.Definitions
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.SmoothCheegerGromovLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedGlobal
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Conditions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow
namespace HamiltonPositiveRicci

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

def hamiltonMetricConnectionFamilyCore
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (g0 : SmoothRiemannianMetric I M) :
    DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun t => by
    classical
    exact if _ht : t ∈ D.carrier then S.family.metric t else g0
  connection := fun t => by
    classical
    exact
      if _ht : t ∈ D.carrier then S.family.connection t
      else DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric (I := I) g0
  metricCompatible := by
    intro t
    classical
    by_cases ht : t ∈ D.carrier
    · simpa [ht] using S.family.metricCompatible ⟨t, ht⟩
    · simpa [ht] using
        (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible
          (I := I) g0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonMetricConnectionFamilyCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonMetricConnectionFamilyCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonMetricConnectionFamilyCore ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonMetricConnectionFamilyCore

structure HamiltonFiniteTimeFlow (g0 : SmoothRiemannianMetric I M) where
  D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval
  S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D
  isSmooth : DifferentialGeometry.PDE.RicciFlow.IsSmoothSolutionOn (I := I) (M := M) S
  startsAt : S.family.metric D.initial = g0
  curvUnbounded : forall K : Real, exists t : Real, exists x : M,
    t ∈ D.carrier /\
      K < Tensor0SBundle.normSq0S (I := I) (S.family.metric t) x 4
        (S.base.rm04 t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonFiniteTimeFlow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonFiniteTimeFlow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonFiniteTimeFlow ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonFiniteTimeFlow

abbrev hamiltonSolution
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) P.D :=
  P.S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonSolution

def hamiltonScalar
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar (I := I) (hamiltonSolution (I := I) P)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonScalar

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem hamilton_scalar_space_time_continuous
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    DifferentialGeometry.PDE.RicciFlow.ScalarSTContOn
      (I := I) (M := M) (hamiltonSolution (I := I) (M := M) P) := by
  exact P.isSmooth.scalarSTCont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_scalar_space_time_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_scalar_space_time_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_scalar_space_time_continuous ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_scalar_space_time_continuous

def hamiltonRiemannNormSq
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0) :
    Real -> M -> Real :=
  fun t x =>
    Tensor0SBundle.normSq0S (I := I)
      ((hamiltonSolution (I := I) (M := M) P).family.metric t) x 4
      (((hamiltonSolution (I := I) (M := M) P).base.rm04 t) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRiemannNormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRiemannNormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRiemannNormSq ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRiemannNormSq

structure HamiltonBlowup (M : Type*) where
  point : Nat -> M
  time : Nat -> Real

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonBlowup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonBlowup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonBlowup ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonBlowup

def hamiltonBlowupScale
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (i : Nat) : Real :=
  hamiltonScalar (I := I) P (Q.time i) (Q.point i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonBlowupScale then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonBlowupScale"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonBlowupScale ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonBlowupScale

def hamiltonRescaledTime
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (i : Nat) (s : Real) : Real :=
  Q.time i + s / hamiltonBlowupScale (I := I) P Q i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledTime ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledTime

def hamiltonRescaledScalar
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (i : Nat) (s : Real) (x : M) : Real :=
  (hamiltonBlowupScale (I := I) P Q i)⁻¹ *
    hamiltonScalar (I := I) P (hamiltonRescaledTime (I := I) P Q i s) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledScalar ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonRescaledScalar

def hamiltonReferenceRadius : Real := (1 : Real) / 10

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonReferenceRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonReferenceRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonReferenceRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonReferenceRadius

theorem hamilton_reference_radius_pos : 0 < hamiltonReferenceRadius := by
  norm_num [hamiltonReferenceRadius]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_reference_radius_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_reference_radius_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_reference_radius_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_reference_radius_pos

structure HamiltonCGHLimit (I : ModelWithCorners Real E H) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H M] where
  N : Type u
  [topology : TopologicalSpace N]
  [charted : ChartedSpace H N]
  [smooth : IsManifold I ∞ N]
  [smooth_plus : IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
  [sigmaCompact : SigmaCompactSpace N]
  [t2 : T2Space N]
  [t2TangentBundle : T2Space (TangentBundle I N)]
  basepoint : N
  D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval
  S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := N) D
  isSolution : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S
  sourceTerm : Nat ->
    DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.{u} (I := I) D
  origIndex : Nat -> Nat
  origStrict : StrictMono origIndex
  cghSubseq : Nat -> Nat
  cghStrict : StrictMono cghSubseq
  cgh : DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges
    (I := I)
    { D := D, term := sourceTerm }
    { M := N, topology := topology, charted := charted, smooth := smooth,
      sigmaCompact := sigmaCompact, t2 := t2,
      t2TangentBundle := t2TangentBundle, basepoint := basepoint,
      S := S, isSolution := isSolution }
    cghSubseq
  sourceToOrig : forall i : Nat,
    letI : TopologicalSpace (sourceTerm i).M := (sourceTerm i).topology
    letI : ChartedSpace H (sourceTerm i).M := (sourceTerm i).charted
    (sourceTerm i).M ≃ₘ⟮I, I⟯ M
  limitComplete : forall t : Real, t ∈ D.carrier ->
    DifferentialGeometry.CheegerGromovCompactness.MetricComplete (I := I)
      { M := N, topology := topology, charted := charted, smooth := smooth,
        sigmaCompact := sigmaCompact, t2 := t2,
        t2TangentBundle := t2TangentBundle, basepoint := basepoint,
        metric := S.base.metric t }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit

namespace HamiltonCGHLimit

abbrev source (L : HamiltonCGHLimit (I := I) M) :
    DifferentialGeometry.CheegerGromovCompactness.PointedFlowSeq.{u} (I := I) :=
  { D := L.D, term := L.sourceTerm }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.source ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.source

abbrev limit (L : HamiltonCGHLimit (I := I) M) :
    DifferentialGeometry.CheegerGromovCompactness.PointedFlowData.{u} (I := I) L.D :=
  { M := L.N, topology := L.topology, charted := L.charted, smooth := L.smooth,
    sigmaCompact := L.sigmaCompact, t2 := L.t2,
    t2TangentBundle := L.t2TangentBundle, basepoint := L.basepoint,
    S := L.S, isSolution := L.isSolution }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.limit ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.limit

def subseq (L : HamiltonCGHLimit (I := I) M) : Nat -> Nat :=
  fun k => L.origIndex (L.cghSubseq k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem subseq_strict (L : HamiltonCGHLimit (I := I) M) :
    StrictMono L.subseq :=
  L.origStrict.comp L.cghStrict

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq_strict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq_strict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq_strict ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.HamiltonCGHLimit.subseq_strict

end HamiltonCGHLimit

def hamiltonLimitConnected (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  ConnectedSpace L.N

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitConnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitConnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitConnected ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitConnected

def hamiltonLimitBoundaryless : Prop := I.Boundaryless

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBoundaryless then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBoundaryless"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBoundaryless ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBoundaryless

def hamiltonLimitBaseScalarConvergence
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M) (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  Filter.Tendsto
    (fun k : Nat =>
      hamiltonRescaledScalar (I := I) P Q (L.subseq k) 0 (Q.point (L.subseq k)))
    Filter.atTop (nhds (L.S.scalar 0 L.basepoint))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBaseScalarConvergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBaseScalarConvergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBaseScalarConvergence ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamiltonLimitBaseScalarConvergence

def limitBaseScalarOne (L : HamiltonCGHLimit (I := I) M) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  L.S.scalar 0 L.basepoint = 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitBaseScalarOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitBaseScalarOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitBaseScalarOne ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitBaseScalarOne

def limitTracefreeRicciZeroAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N,
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciZeroAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciZeroAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciZeroAt ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciZeroAt

def limitTracefreeRicciDecayAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall η : Real, 0 < η ->
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x <= η

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciDecayAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciDecayAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciDecayAt ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitTracefreeRicciDecayAt

def limitEinsteinAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  forall x : L.N, forall v w : TangentSpace I x,
    L.S.ricciAt t x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
      (L.S.scalar t x / 3) * (L.S.base.metric t).inner x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitEinsteinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitEinsteinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitEinsteinAt ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitEinsteinAt

def limitRoundAt (L : HamiltonCGHLimit (I := I) M) (t : Real) : Prop :=
  letI : TopologicalSpace L.N := L.topology
  letI : ChartedSpace H L.N := L.charted
  letI : IsManifold I ∞ L.N := L.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  letI : SigmaCompactSpace L.N := L.sigmaCompact
  letI : T2Space L.N := L.t2
  let g := L.S.base.metric t
  exists K : Real, 0 < K /\
    (forall x : L.N, forall v : TangentSpace I x,
      (((Module.finrank Real E : Real) - 1) * K) * g.inner x v v <=
        DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) g x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /\
    constantPositiveSectionalCurvatureMetric (I := I) (M := L.N) g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitRoundAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitRoundAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitRoundAt ``Submission.DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.limitRoundAt


end HamiltonPositiveRicci
end DifferentialGeometry.PDE.RicciFlow
