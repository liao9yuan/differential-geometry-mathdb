import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Defs
import Submission.DifferentialGeometry.Topology.Exhaustion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite
namespace CheegerGromovCompactness

open scoped _root_.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

structure PointedCGHMaps
    (X : PointedFlowSeq (I := I))
    (P : PointedRiemannianManifold (I := I))
    (subseq : Nat -> Nat) where
  partialDiffeomorph :
    forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      PartialDiffeomorph I I P.M (X.term (subseq k)).M (∞ : WithTop ℕ∞)
  source_exhausts :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    ExhaustsByOpen (fun k =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      (partialDiffeomorph k).source)
  base_mem :
    forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      P.basepoint ∈ (partialDiffeomorph k).source
  basepoint_map :
    forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      partialDiffeomorph k P.basepoint = (X.term (subseq k)).basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps

namespace PointedCGHMaps

def compSubseq
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedCGHMaps (I := I) X P (subseq ∘ φ) where
  partialDiffeomorph k := Φ.partialDiffeomorph (φ k)
  source_exhausts := by
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    exact Φ.source_exhausts.comp_subseq hφ
  base_mem k := Φ.base_mem (φ k)
  basepoint_map k := Φ.basepoint_map (φ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq

def source
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) : Set P.M := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source

def target
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    Set ((X.term (subseq k)).M) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target

def map
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    P.M -> (X.term (subseq k)).M := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact fun x => (Φ.partialDiffeomorph k) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.map ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.map

@[simp] theorem compSubseq_source
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat) :
    (Φ.compSubseq φ hφ).source k = Φ.source (φ k) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_source

@[simp] theorem compSubseq_target
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat) :
    (Φ.compSubseq φ hφ).target k = Φ.target (φ k) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_target ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_target

@[simp] theorem compSubseq_map
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat) :
    (Φ.compSubseq φ hφ).map k = Φ.map (φ k) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_map ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.compSubseq_map

theorem source_open
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace P.M := P.topology
    IsOpen (Φ.source k) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_source

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_open ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_open

theorem target_open
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    IsOpen (Φ.target k) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  exact (Φ.partialDiffeomorph k).open_target

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target_open then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target_open"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target_open ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.target_open

theorem source_mono
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace P.M := P.topology
    Φ.source k ⊆ Φ.source (k + 1) := by
  let : TopologicalSpace P.M := P.topology
  exact Φ.source_exhausts.mono_step k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_mono ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_mono

theorem source_subset
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    {K : Set P.M}
    (hK :
      letI : TopologicalSpace P.M := P.topology
      IsCompact K) :
    exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k := by
  let : TopologicalSpace P.M := P.topology
  exact Φ.source_exhausts.subset K hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_subset ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGHMaps.source_subset

end PointedCGHMaps

def sourceOpen
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace P.M := P.topology
    TopologicalSpace.Opens P.M := by
  letI : TopologicalSpace P.M := P.topology
  exact ⟨Φ.source k, Φ.source_open k⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceOpen

def targetOpen
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    TopologicalSpace.Opens ((X.term (subseq k)).M) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  exact ⟨Φ.target k, Φ.target_open k⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetOpen ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetOpen

abbrev SourceDomain
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :=
  letI : TopologicalSpace P.M := P.topology
  (sourceOpen (I := I) Φ k : Type _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceDomain ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceDomain

abbrev TargetDomain
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :=
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  (targetOpen (I := I) Φ k : Type _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.TargetDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.TargetDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.TargetDomain ``Submission.DifferentialGeometry.CheegerGromovCompactness.TargetDomain

@[implicit_reducible]
noncomputable def sourceDomTop
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    TopologicalSpace (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  change TopologicalSpace (sourceOpen (I := I) Φ k)
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceDomTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceDomTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceDomTop ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceDomTop

@[implicit_reducible]
noncomputable def sourceDomCharted
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    ChartedSpace H (SourceDomain (I := I) Φ k) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  change ChartedSpace H (sourceOpen (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H) (M := P.M)
    (s := sourceOpen (I := I) Φ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceDomCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceDomCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceDomCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceDomCharted

theorem sourceDomT2
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    T2Space (SourceDomain (I := I) Φ k) := by
  let : TopologicalSpace P.M := P.topology
  let : T2Space P.M := P.t2
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  change T2Space {x : P.M // x ∈ Φ.source k}
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceDomT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceDomT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceDomT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceDomT2

theorem sourceDomSmooth
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    IsManifold I ∞ (SourceDomain (I := I) Φ k) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  change IsManifold I ∞ (sourceOpen (I := I) Φ k)
  exact { (sourceOpen (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceDomSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceDomSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceDomSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceDomSmooth

theorem sourceDomSigmaOf
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσ : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k)) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    SigmaCompactSpace (SourceDomain (I := I) Φ k) := by
  let : TopologicalSpace P.M := P.topology
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  change SigmaCompactSpace {x : P.M // x ∈ Φ.source k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceDomSigmaOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceDomSigmaOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceDomSigmaOf ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceDomSigmaOf

@[implicit_reducible]
noncomputable def targetDomTop
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    TopologicalSpace (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  change TopologicalSpace (targetOpen (I := I) Φ k)
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetDomTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetDomTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetDomTop ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetDomTop

@[implicit_reducible]
noncomputable def targetDomCharted
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    ChartedSpace H (TargetDomain (I := I) Φ k) := by
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  change ChartedSpace H (targetOpen (I := I) Φ k)
  exact TopologicalSpace.Opens.instChartedSpace (H := H)
    (M := (X.term (subseq k)).M) (s := targetOpen (I := I) Φ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetDomCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetDomCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetDomCharted ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetDomCharted

theorem targetDomT2
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    T2Space (TargetDomain (I := I) Φ k) := by
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  let : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  change T2Space {x : (X.term (subseq k)).M // x ∈ Φ.target k}
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetDomT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetDomT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetDomT2 ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetDomT2

theorem targetDomSmooth
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    IsManifold I ∞ (TargetDomain (I := I) Φ k) := by
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  let : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  let : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  let : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  change IsManifold I ∞ (targetOpen (I := I) Φ k)
  exact { (targetOpen (I := I) Φ k).instHasGroupoid (contDiffGroupoid ∞ I) with }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetDomSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetDomSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetDomSmooth ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetDomSmooth

theorem targetDomSigmaOf
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (hσ :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsSigmaCompact (Φ.target k)) :
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    SigmaCompactSpace (TargetDomain (I := I) Φ k) := by
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  change SigmaCompactSpace {x : (X.term (subseq k)).M // x ∈ Φ.target k}
  exact isSigmaCompact_iff_sigmaCompactSpace.mp hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetDomSigmaOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetDomSigmaOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetDomSigmaOf ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetDomSigmaOf

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem contMDiff_openCod
    {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold I ∞ M] [IsManifold I ∞ N]
    {U : TopologicalSpace.Opens N}
    {f : M -> U}
    (hf : ContMDiff I I (∞ : WithTop ℕ∞) (fun x : M => (f x : N))) :
    ContMDiff I I (∞ : WithTop ℕ∞) f := by
  have : IsManifold I ∞ U :=
    { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  rw [contMDiff_iff_target] at hf ⊢
  constructor
  · exact Continuous.subtype_mk hf.1 (fun x => (f x).2)
  · intro y
    have hy := hf.2 (y : N)
    simpa [Function.comp_def, extChartAt, TopologicalSpace.Opens.chartAt_eq,
      Set.preimage_preimage] using hy

run_cmd do
  let target := ``Submission.DifferentialGeometry.CheegerGromovCompactness.contMDiff_openCod
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.CheegerGromovCompactness.contMDiff_openCod target :: scope.openDecls } }

noncomputable def sourceTargetDiff
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    Diffeomorph I I (SourceDomain (I := I) Φ k) (TargetDomain (I := I) Φ k)
      (∞ : WithTop ℕ∞) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  let e := Φ.partialDiffeomorph k
  refine
    { toEquiv := e.toPartialEquiv.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun x : SourceDomain (I := I) Φ k => e (x : P.M)) := by
      intro x
      have hx : (x : P.M) ∈ e.source := x.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞) (fun y : P.M => e y) (x : P.M) :=
        e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx)
      exact (contMDiffAt_subtype_iff
        (U := sourceOpen (I := I) Φ k)
        (f := fun y : P.M => e y) (x := x)).2 hAt
    exact contMDiff_openCod (I := I) (U := targetOpen (I := I) Φ k) hbase
  · have hbase :
        ContMDiff I I (∞ : WithTop ℕ∞)
          (fun y : TargetDomain (I := I) Φ k => e.toPartialEquiv.symm
            (y : (X.term (subseq k)).M)) := by
      intro y
      have hy : (y : (X.term (subseq k)).M) ∈ e.target := y.2
      have hAt :
          ContMDiffAt I I (∞ : WithTop ℕ∞)
            (fun z : (X.term (subseq k)).M => e.toPartialEquiv.symm z)
            (y : (X.term (subseq k)).M) :=
        e.contMDiffOn_invFun.contMDiffAt (e.open_target.mem_nhds hy)
      exact (contMDiffAt_subtype_iff
        (U := targetOpen (I := I) Φ k)
            (f := fun z : (X.term (subseq k)).M => e.toPartialEquiv.symm z) (x := y)).2 hAt
    exact contMDiff_openCod (I := I) (U := sourceOpen (I := I) Φ k) hbase

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff

@[simp]
theorem sourceTargetDiff_apply
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (x : SourceDomain (I := I) Φ k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    (sourceTargetDiff (I := I) Φ k x : (X.term (subseq k)).M) = Φ.map k (x : P.M) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_apply ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_apply

@[simp]
theorem sourceTargetDiff_symm_apply
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (y : TargetDomain (I := I) Φ k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
    letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
    letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
    ((sourceTargetDiff (I := I) Φ k).symm y : P.M) =
      (Φ.partialDiffeomorph k).toPartialEquiv.symm (y : (X.term (subseq k)).M) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_symm_apply ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceTargetDiff_symm_apply

def sourceCompactSet
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (K : Set P.M) : Set (SourceDomain (I := I) Φ k) :=
  {x | (x : P.M) ∈ K}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet

def targetCompactSet
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    (K : Set (X.term (subseq k)).M) : Set (TargetDomain (I := I) Φ k) :=
  {x | (x : (X.term (subseq k)).M) ∈ K}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetCompactSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetCompactSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetCompactSet ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetCompactSet

theorem sourceCompactSet_isCompact
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    {K : Set P.M}
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (hKsrc : letI : TopologicalSpace P.M := P.topology; K ⊆ Φ.source k) :
    letI : TopologicalSpace P.M := P.topology
    IsCompact (sourceCompactSet (I := I) Φ k K) := by
  let : TopologicalSpace P.M := P.topology
  change IsCompact ((Subtype.val : SourceDomain (I := I) Φ k -> P.M) ⁻¹' K)
  rw [Subtype.isCompact_iff]
  have hImage :
      Subtype.val '' ((Subtype.val : SourceDomain (I := I) Φ k -> P.M) ⁻¹' K) = K := by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact hyK
    · intro hxK
      exact ⟨⟨x, hKsrc hxK⟩, hxK, rfl⟩
  rw [hImage]
  exact hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet_isCompact ``Submission.DifferentialGeometry.CheegerGromovCompactness.sourceCompactSet_isCompact

theorem targetCompactSet_isCompact
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat)
    {K : Set (X.term (subseq k)).M}
    (hK :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      IsCompact K)
    (hKtgt :
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      K ⊆ Φ.target k) :
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    IsCompact (targetCompactSet (I := I) Φ k K) := by
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  change IsCompact ((Subtype.val : TargetDomain (I := I) Φ k ->
      (X.term (subseq k)).M) ⁻¹' K)
  rw [Subtype.isCompact_iff]
  have hImage :
      Subtype.val '' ((Subtype.val : TargetDomain (I := I) Φ k ->
        (X.term (subseq k)).M) ⁻¹' K) = K := by
    ext x
    constructor
    · rintro ⟨y, hyK, rfl⟩
      exact hyK
    · intro hxK
      exact ⟨⟨x, hKtgt hxK⟩, hxK, rfl⟩
  rw [hImage]
  exact hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.targetCompactSet_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.targetCompactSet_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.targetCompactSet_isCompact ``Submission.DifferentialGeometry.CheegerGromovCompactness.targetCompactSet_isCompact

structure SourceDomainMetricData
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) (k : Nat) where
  topology : TopologicalSpace (SourceDomain (I := I) Φ k)
  charted : ChartedSpace H (SourceDomain (I := I) Φ k)
  t2 : T2Space (SourceDomain (I := I) Φ k)
  smooth : IsManifold I ∞ (SourceDomain (I := I) Φ k)
  sigmaCompact : SigmaCompactSpace (SourceDomain (I := I) Φ k)
  limitMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  pullbackMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  referenceMetric :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k)
  limitMetricFamily :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real -> SmoothRiemannianMetric I P.M
  compact_preimage :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : TopologicalSpace P.M := P.topology
    forall K : Set P.M, IsCompact K ->
      K ⊆ Φ.source k ->
      IsCompact (sourceCompactSet (I := I) Φ k K)
  limit_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M
      infer_instance
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (limitMetric t).inner x v w =
          (limitMetricFamily t).inner (x : P.M)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v)
            ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w)
  pullback_inner :
    letI : TopologicalSpace (SourceDomain (I := I) Φ k) := topology
    letI : ChartedSpace H (SourceDomain (I := I) Φ k) := charted
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
      change IsManifold I ∞ P.M
      infer_instance
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
      by
        change IsManifold I ∞ (X.term (subseq k)).M
        infer_instance
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    forall (t : Real) (x : SourceDomain (I := I) Φ k)
      (v w : TangentSpace I x),
        (pullbackMetric t).inner x v w =
          ((X.term (subseq k)).S.family.metric t).inner
            (Φ.map k (x : P.M))
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) v)
            ((mfderiv I I
              (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData

namespace SourceDomainMetricData

noncomputable def ofCanonical
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {k : Nat}
    (sigmaCompact :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      SigmaCompactSpace (SourceDomain (I := I) Φ k))
    (limitMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (pullbackMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (referenceMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (limit_inner :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      forall (t : Real) (x : SourceDomain (I := I) Φ k)
        (v w : TangentSpace I x),
          (limitMetric t).inner x v w =
            (limitMetricFamily t).inner (x : P.M)
              ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v)
              ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w))
    (pullback_inner :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : T2Space P.M := P.t2
      letI : IsManifold I ∞ P.M := P.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
        change IsManifold I ∞ P.M
        infer_instance
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        by
          change IsManifold I ∞ (X.term (subseq k)).M
          infer_instance
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      forall (t : Real) (x : SourceDomain (I := I) Φ k)
        (v w : TangentSpace I x),
          (pullbackMetric t).inner x v w =
            ((X.term (subseq k)).S.family.metric t).inner
              (Φ.map k (x : P.M))
              ((mfderiv I I
                (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) v)
              ((mfderiv I I
                (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) w)) :
    SourceDomainMetricData (I := I) Φ k where
  topology := sourceDomTop (I := I) Φ k
  charted := sourceDomCharted (I := I) Φ k
  t2 := sourceDomT2 (I := I) Φ k
  smooth := sourceDomSmooth (I := I) Φ k
  sigmaCompact := sigmaCompact
  limitMetric := limitMetric
  pullbackMetric := pullbackMetric
  referenceMetric := referenceMetric
  limitMetricFamily := limitMetricFamily
  compact_preimage := by
    intro K hK hKsrc
    exact sourceCompactSet_isCompact (I := I) Φ k hK hKsrc
  limit_inner := limit_inner
  pullback_inner := pullback_inner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofCanonical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofCanonical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofCanonical ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofCanonical

noncomputable def ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {k : Nat}
    (hσsource : letI : TopologicalSpace P.M := P.topology; IsSigmaCompact (Φ.source k))
    (referenceMetric :
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M) :
    SourceDomainMetricData (I := I) Φ k := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  letI : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
  letI : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
    change IsManifold I ∞ (X.term (subseq k)).M
    infer_instance
  letI : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k hσsource
  letI : TopologicalSpace (TargetDomain (I := I) Φ k) := targetDomTop (I := I) Φ k
  letI : ChartedSpace H (TargetDomain (I := I) Φ k) := targetDomCharted (I := I) Φ k
  letI : T2Space (TargetDomain (I := I) Φ k) := targetDomT2 (I := I) Φ k
  letI : IsManifold I ∞ (TargetDomain (I := I) Φ k) := targetDomSmooth (I := I) Φ k
  refine SourceDomainMetricData.ofCanonical (I := I)
    (Φ := Φ) (k := k)
    (sourceDomSigmaOf (I := I) Φ k hσsource)
    (fun t => by
      let sourceT2 : T2Space (sourceOpen (I := I) Φ k) := by
        change T2Space (SourceDomain (I := I) Φ k)
        exact sourceDomT2 (I := I) Φ k
      exact
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          P.M P.topology P.charted P.smooth inferInstance
          (limitMetricFamily t) (sourceOpen (I := I) Φ k) sourceT2)
    (fun t => by
      let sourceT2 : T2Space (sourceOpen (I := I) Φ k) := by
        change T2Space (SourceDomain (I := I) Φ k)
        exact sourceDomT2 (I := I) Φ k
      let targetT2 : T2Space (targetOpen (I := I) Φ k) := by
        change T2Space (TargetDomain (I := I) Φ k)
        exact targetDomT2 (I := I) Φ k
      let targetMetric : SmoothRiemannianMetric I (targetOpen (I := I) Φ k) :=
        @SmoothRiemannianMetric.restrictOpen E inferInstance inferInstance H inferInstance I
          (X.term (subseq k)).M (X.term (subseq k)).topology
          (X.term (subseq k)).charted (X.term (subseq k)).smooth inferInstance
          ((X.term (subseq k)).S.family.metric t) (targetOpen (I := I) Φ k)
          targetT2
      exact
        @Diffeomorph.pullbackMetric E inferInstance inferInstance inferInstance H inferInstance I
          (SourceDomain (I := I) Φ k) (sourceDomTop (I := I) Φ k)
          (sourceDomCharted (I := I) Φ k) (sourceDomSmooth (I := I) Φ k)
          (TargetDomain (I := I) Φ k) (targetDomTop (I := I) Φ k)
          (targetDomCharted (I := I) Φ k) (targetDomSmooth (I := I) Φ k)
          sourceT2 targetMetric (sourceTargetDiff (I := I) Φ k))
    referenceMetric
    limitMetricFamily
    ?_ ?_
  · intro t x v w
    change (limitMetricFamily t).inner (x : P.M) v w =
      (limitMetricFamily t).inner (x : P.M)
        ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v)
        ((mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w)
    have hvinc :
        (mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) v = v := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Φ k) x v
    have hwinc :
        (mfderiv I I (fun y : SourceDomain (I := I) Φ k => (y : P.M)) x) w = w := by
      simpa only using
        mfderiv_subtype_val_apply (I := I) (sourceOpen (I := I) Φ k) x w
    rw [hvinc, hwinc]
  · intro t x v w
    rw [Diffeomorph.pullbackMetric_inner]
    change ((X.term (subseq k)).S.family.metric t).inner
        ((sourceTargetDiff (I := I) Φ k x : TargetDomain (I := I) Φ k) :
          (X.term (subseq k)).M)
        ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v)
        ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w) =
      ((X.term (subseq k)).S.family.metric t).inner
        (Φ.map k (x : P.M))
        ((mfderiv I I
          (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) v)
        ((mfderiv I I
          (fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M)) x) w)
    have hchain :
        mfderiv I I
            (fun y : SourceDomain (I := I) Φ k =>
              ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
                (X.term (subseq k)).M)) x =
          (mfderiv I I
              (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
              (sourceTargetDiff (I := I) Φ k x)).comp
            (mfderiv I I (sourceTargetDiff (I := I) Φ k) x) := by
      have hval :
          MDifferentiableAt I I
            (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
            (sourceTargetDiff (I := I) Φ k x) := by
        exact ContMDiffAt.mdifferentiableAt
          ((contMDiff_subtype_val (I := I) (n := (∞ : WithTop ℕ∞))
            (U := targetOpen (I := I) Φ k)).contMDiffAt)
          (by simp)
      have hdiff :
          MDifferentiableAt I I (sourceTargetDiff (I := I) Φ k)
            x :=
        (sourceTargetDiff (I := I) Φ k).contMDiff.contMDiffAt.mdifferentiableAt
          (by simp)
      simpa [Function.comp_def] using
        (mfderiv_comp (I := I) (I' := I) (I'' := I) x hval hdiff)
    have hv :
        mfderiv I I
            (fun y : SourceDomain (I := I) Φ k =>
              ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
                (X.term (subseq k)).M)) x v =
          mfderiv I I (sourceTargetDiff (I := I) Φ k) x v := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
              (sourceTargetDiff (I := I) Φ k x))
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v) =
            (mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (targetOpen (I := I) Φ k)
            (sourceTargetDiff (I := I) Φ k x)
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) v)
      exact htarget
    have hw :
        mfderiv I I
            (fun y : SourceDomain (I := I) Φ k =>
              ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
                (X.term (subseq k)).M)) x w =
          mfderiv I I (sourceTargetDiff (I := I) Φ k) x w := by
      rw [hchain, ContinuousLinearMap.comp_apply]
      have htarget :
          (mfderiv I I
              (fun y : TargetDomain (I := I) Φ k => (y : (X.term (subseq k)).M))
              (sourceTargetDiff (I := I) Φ k x))
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w) =
            (mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w := by
        simpa only using
          mfderiv_subtype_val_apply (I := I) (targetOpen (I := I) Φ k)
            (sourceTargetDiff (I := I) Φ k x)
            ((mfderiv I I (sourceTargetDiff (I := I) Φ k) x) w)
      exact htarget
    have hxmap :
        ((sourceTargetDiff (I := I) Φ k x : TargetDomain (I := I) Φ k) :
          (X.term (subseq k)).M) = Φ.map k (x : P.M) :=
      sourceTargetDiff_apply (I := I) Φ k x
    have hfun :
        (fun y : SourceDomain (I := I) Φ k =>
          ((sourceTargetDiff (I := I) Φ k y : TargetDomain (I := I) Φ k) :
            (X.term (subseq k)).M)) =
          fun y : SourceDomain (I := I) Φ k => Φ.map k (y : P.M) := by
      funext y
      exact sourceTargetDiff_apply (I := I) Φ k y
    rw [hxmap, ← hv, ← hw, hfun]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofRestrictPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofRestrictPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofRestrictPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.ofRestrictPullback

noncomputable def derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {k : Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (D : SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M) (p : Nat) (t : Real) : Real := by
  letI : TopologicalSpace (SourceDomain (I := I) Φ k) := D.topology
  letI : ChartedSpace H (SourceDomain (I := I) Φ k) := D.charted
  letI : T2Space (SourceDomain (I := I) Φ k) := D.t2
  letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := D.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
      (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) := D.sigmaCompact
  exact metricDerivNormSupOn (I := I)
    (sourceCompactSet (I := I) Φ k K) p
    (D.pullbackMetric t) (D.limitMetric t) (D.referenceMetric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.derivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.derivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.derivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceDomainMetricData.derivNormSupOn

end SourceDomainMetricData

def SourceMetricCPConvergenceOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M)
    (p : Nat) (t : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        (D k).derivNormSupOn (I := I) K p t < ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOn

def SourceMetricCPConvergenceOnWindow
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k)
    (K : Set P.M)
    (p : Nat)
    (a b : Real) : Prop :=
  forall ε : Real, 0 < ε ->
    exists k0 : Nat, forall k : Nat, k0 <= k ->
      K ⊆ Φ.source k /\
        forall t : Real, t ∈ Set.Icc a b ->
          (D k).derivNormSupOn (I := I) K p t < ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow

theorem SourceMetricCPConvergenceOnWindow.of_derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    {K : Set P.M}
    (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    {p : Nat} {a b : Real}
    (hconv : forall ε : Real, 0 < ε ->
      exists k0 : Nat, forall k : Nat, k0 <= k ->
        forall t : Real, t ∈ Set.Icc a b ->
          (D k).derivNormSupOn (I := I) K p t < ε) :
    SourceMetricCPConvergenceOnWindow (I := I) Φ D K p a b := by
  intro ε hε
  obtain ⟨kSource, hSource⟩ := Φ.source_subset hK
  obtain ⟨kConvergence, hConvergence⟩ := hconv ε hε
  refine ⟨max kSource kConvergence, fun k hk => ?_⟩
  refine ⟨hSource k (le_trans (Nat.le_max_left kSource kConvergence) hk), ?_⟩
  exact hConvergence k (le_trans (Nat.le_max_right kSource kConvergence) hk)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow.of_derivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow.of_derivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow.of_derivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricCPConvergenceOnWindow.of_derivNormSupOn

structure SourceMetricConvergenceData
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq) where
  domain : forall k : Nat, SourceDomainMetricData (I := I) Φ k
  converges :
    forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        SourceMetricCPConvergenceOn (I := I) Φ domain K p t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData

namespace SourceMetricConvergenceData

noncomputable def ofDerivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            (D k).derivNormSupOn (I := I) K p t < ε) :
    SourceMetricConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p t ht ε hε
    obtain ⟨kSource, hSource⟩ := Φ.source_subset hK
    obtain ⟨kConvergence, hConvergence⟩ := hconv K hK p t ht ε hε
    refine ⟨max kSource kConvergence, fun k hk => ?_⟩
    refine ⟨hSource k (le_trans (Nat.le_max_left kSource kConvergence) hk), ?_⟩
    exact hConvergence k (le_trans (Nat.le_max_right kSource kConvergence) hk)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofDerivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofDerivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofDerivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofDerivNormSupOn

noncomputable def ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (hσsource : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall t : Real, t ∈ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            ((SourceDomainMetricData.ofRestrictPullback (I := I)
              (Φ := Φ) (k := k) (hσsource k)
              (referenceMetric k) limitMetricFamily).derivNormSupOn (I := I) K p t) < ε) :
    SourceMetricConvergenceData (I := I) Φ :=
  SourceMetricConvergenceData.ofDerivNormSupOn (I := I)
    (D := fun k => SourceDomainMetricData.ofRestrictPullback (I := I)
      (Φ := Φ) (k := k) (hσsource k) (referenceMetric k) limitMetricFamily)
    hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofRestrictPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofRestrictPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofRestrictPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceMetricConvergenceData.ofRestrictPullback

end SourceMetricConvergenceData

structure SourceSpacetimeConvergenceData
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (D : forall k : Nat, SourceDomainMetricData (I := I) Φ k) where
  converges_on_windows :
    forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        SourceMetricCPConvergenceOnWindow (I := I) Φ D K p a b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData

namespace SourceSpacetimeConvergenceData

noncomputable def toSpatial
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (Hst : SourceSpacetimeConvergenceData (I := I) Φ D) :
    SourceMetricConvergenceData (I := I) Φ where
  domain := D
  converges := by
    intro K hK p t ht ε hε
    have hwin : Set.Icc t t ⊆ X.D.carrier := by
      intro s hs
      have hst : s = t := le_antisymm hs.2 hs.1
      simpa [hst] using ht
    obtain ⟨k0, hk0⟩ := Hst.converges_on_windows K hK p t t hwin ε hε
    refine ⟨k0, fun k hk => ?_⟩
    obtain ⟨hsrc, hbound⟩ := hk0 k hk
    exact ⟨hsrc, hbound t ⟨le_rfl, le_rfl⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.toSpatial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.toSpatial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.toSpatial ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.toSpatial

theorem of_derivNormSupOn
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t : Real, t ∈ Set.Icc a b ->
              (D k).derivNormSupOn (I := I) K p t < ε) :
    SourceSpacetimeConvergenceData (I := I) Φ D where
  converges_on_windows := by
    intro K hK p a b hwin
    exact SourceMetricCPConvergenceOnWindow.of_derivNormSupOn (I := I) hK
      (hconv K hK p a b hwin)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.of_derivNormSupOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.of_derivNormSupOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.of_derivNormSupOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.of_derivNormSupOn

theorem ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    (hσsource : forall k : Nat,
      letI : TopologicalSpace P.M := P.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M)
    (hconv : forall K : Set P.M,
      forall _hK : letI : TopologicalSpace P.M := P.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t : Real, t ∈ Set.Icc a b ->
              ((SourceDomainMetricData.ofRestrictPullback (I := I)
                (Φ := Φ) (k := k) (hσsource k)
                (referenceMetric k) limitMetricFamily).derivNormSupOn (I := I) K p t) < ε) :
    SourceSpacetimeConvergenceData (I := I) Φ
      (fun k => SourceDomainMetricData.ofRestrictPullback (I := I)
        (Φ := Φ) (k := k) (hσsource k) (referenceMetric k) limitMetricFamily) :=
  SourceSpacetimeConvergenceData.of_derivNormSupOn (I := I) hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.ofRestrictPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.ofRestrictPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.ofRestrictPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.SourceSpacetimeConvergenceData.ofRestrictPullback

end SourceSpacetimeConvergenceData

def FunctionPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real)
    (uInf : Real -> P.M -> Real) : Prop :=
  ∀ t ∈ X.D.carrier, forall x : P.M,
    Filter.Tendsto (fun k : Nat => uSeq k t (Phi.map k x))
      Filter.atTop (nhds (uInf t x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto

theorem FunctionPullbackTendsto.le_of_bound0
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedCGHMaps (I := I) X P subseq}
    {uSeq : forall k : Nat, Real -> (X.term (subseq k)).M -> Real}
    {uInf : Real -> P.M -> Real}
    (hconv : FunctionPullbackTendsto (I := I) Phi uSeq uInf)
    (bound : Real -> P.M -> Nat -> Real)
    (hbound :
      forall t : Real, forall x : P.M,
        Filter.Tendsto (bound t x) Filter.atTop (nhds 0) /\
          (∀ᶠ k in Filter.atTop,
            uSeq k t (Phi.map k x) <= bound t x k)) :
    ∀ t ∈ X.D.carrier, forall x : P.M, forall η : Real, 0 < η ->
      uInf t x <= η := by
  intro t ht x η hη
  have hle0 : uInf t x <= 0 := by
    exact le_of_tendsto_of_tendsto (hconv t ht x) (hbound t x).1 (hbound t x).2
  exact le_trans hle0 (le_of_lt hη)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto.le_of_bound0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto.le_of_bound0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto.le_of_bound0 ``Submission.DifferentialGeometry.CheegerGromovCompactness.FunctionPullbackTendsto.le_of_bound0

def ScalarPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq) : Prop :=
  FunctionPullbackTendsto (I := I) Phi
    (fun k t x =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        by
          change IsManifold I ∞ (X.term (subseq k)).M
          infer_instance
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      (X.term (subseq k)).S.scalar t x)
    (fun t x =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
        change IsManifold I ∞ L.M
        infer_instance
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : T2Space L.M := L.t2
      L.S.scalar t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.ScalarPullbackTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.ScalarPullbackTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.ScalarPullbackTendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.ScalarPullbackTendsto

def MetricInnerPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X P subseq)
    (gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M) : Prop :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  ∀ t ∈ X.D.carrier, ∀ x : P.M, ∀ v w : TangentSpace I x,
    Filter.Tendsto
      (fun k =>
        letI : TopologicalSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M :=
          (X.term (subseq k)).charted
        letI : IsManifold I ∞ (X.term (subseq k)).M :=
          (X.term (subseq k)).smooth
        letI : T2Space (TangentBundle I (X.term (subseq k)).M) :=
          (X.term (subseq k)).t2TangentBundle
        ((X.term (subseq k)).S.family.metric t).inner (Phi.map k x)
          (mfderiv I I (Phi.map k) x v)
          (mfderiv I I (Phi.map k) x w))
      Filter.atTop (nhds ((gInf t).inner x v w))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto

def MetricPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq) : Prop :=
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (L.atTime 0).M := L.topology
  letI : ChartedSpace H (L.atTime 0).M := L.charted
  letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
  MetricInnerPullbackTendsto (I := I) Phi L.S.family.metric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricPullbackTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricPullbackTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricPullbackTendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricPullbackTendsto

theorem MetricInnerPullbackTendsto.congr_metric
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Phi : PointedCGHMaps (I := I) X P subseq}
    {g₁ g₂ : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (hmetric : ∀ t, t ∈ X.D.carrier → g₁ t = g₂ t)
    (h₁ : MetricInnerPullbackTendsto (I := I) Phi g₁) :
    MetricInnerPullbackTendsto (I := I) Phi g₂ := by
  intro t ht x v w
  rw [← hmetric t ht]
  exact h₁ t ht x v w

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto.congr_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto.congr_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto.congr_metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricInnerPullbackTendsto.congr_metric

def MetricRicciPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M) : Prop :=
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  ∀ t ∈ X.D.carrier, ∀ x : P.M, ∀ v w : TangentSpace I x,
    Filter.Tendsto
      (fun k =>
        letI : TopologicalSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M :=
          (X.term (subseq k)).charted
        letI : IsManifold I ∞ (X.term (subseq k)).M :=
          (X.term (subseq k)).smooth
        letI : T2Space (X.term (subseq k)).M :=
          (X.term (subseq k)).t2
        Geometry.Curvature.metricRicciAt (I := I)
          ((X.term (subseq k)).S.family.metric t) (Φ.map k x)
          (Geometry.Curvature.vec2
            (mfderiv I I (Φ.map k) x v)
            (mfderiv I I (Φ.map k) x w)))
      Filter.atTop
      (nhds (Geometry.Curvature.metricRicciAt (I := I) (gInf t) x
          (Geometry.Curvature.vec2 v w)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto

theorem MetricRicciPullbackTendsto.congr_metric
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedCGHMaps (I := I) X P subseq}
    {g₁ g₂ : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    (hmetric : ∀ t, t ∈ X.D.carrier → g₁ t = g₂ t)
    (h₁ : MetricRicciPullbackTendsto (I := I) Φ g₁) :
    MetricRicciPullbackTendsto (I := I) Φ g₂ := by
  intro t ht x v w
  rw [← hmetric t ht]
  exact h₁ t ht x v w

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto.congr_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto.congr_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto.congr_metric ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricRicciPullbackTendsto.congr_metric

def RicciPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq) : Prop :=
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (L.atTime 0).M := L.topology
  letI : ChartedSpace H (L.atTime 0).M := L.charted
  letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
  MetricRicciPullbackTendsto (I := I) Φ L.S.family.metric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.RicciPullbackTendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.RicciPullbackTendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.RicciPullbackTendsto ``Submission.DifferentialGeometry.CheegerGromovCompactness.RicciPullbackTendsto

def RicNormPullback
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq) : Prop :=
  FunctionPullbackTendsto (I := I) Phi
    (fun k t x =>
      letI : TopologicalSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M :=
        (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M :=
        (X.term (subseq k)).smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M :=
        by
          change IsManifold I ∞ (X.term (subseq k)).M
          infer_instance
      letI : SigmaCompactSpace (X.term (subseq k)).M :=
        (X.term (subseq k)).sigmaCompact
      letI : T2Space (X.term (subseq k)).M :=
        (X.term (subseq k)).t2
      PDE.RicciFlow.ricciNorm (I := I) (X.term (subseq k)).S t x)
    (fun t x =>
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
        change IsManifold I ∞ L.M
        infer_instance
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      letI : T2Space L.M := L.t2
      PDE.RicciFlow.ricciNorm (I := I) L.S t x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.RicNormPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.RicNormPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.RicNormPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.RicNormPullback

structure PointedCGConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  maps : PointedCGHMaps (I := I) X (L.atTime 0) subseq
  metrics : SourceMetricConvergenceData (I := I) maps

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedCGConverges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedCGConverges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedCGConverges ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedCGConverges

structure SmoothCGHConverges
    (X : PointedFlowSeq (I := I))
    (L : PointedFlowData (I := I) X.D)
    (subseq : Nat -> Nat) where
  spatial : PointedCGConverges (I := I) X L subseq
  metric_converges : MetricPullbackTendsto (I := I) spatial.maps
  scalar_converges : ScalarPullbackTendsto (I := I) spatial.maps
  ricci_converges : RicciPullbackTendsto (I := I) spatial.maps
  ricciNorm_converges : RicNormPullback (I := I) spatial.maps
  spacetime :
    SourceSpacetimeConvergenceData (I := I) spatial.maps
      spatial.metrics.domain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges

namespace SmoothCGHConverges

noncomputable def ofSpacetime
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    {D : forall k : Nat, SourceDomainMetricData (I := I) Φ k}
    (hmetric : MetricPullbackTendsto (I := I) Φ)
    (hscalar : ScalarPullbackTendsto (I := I) Φ)
    (hricci : RicciPullbackTendsto (I := I) Φ)
    (hric : RicNormPullback (I := I) Φ)
    (Hst : SourceSpacetimeConvergenceData (I := I) Φ D) :
    SmoothCGHConverges (I := I) X L subseq where
  spatial := {
    maps := Φ
    metrics := Hst.toSpatial (I := I) }
  metric_converges := hmetric
  scalar_converges := hscalar
  ricci_converges := hricci
  ricciNorm_converges := hric
  spacetime := Hst

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofSpacetime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofSpacetime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofSpacetime ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofSpacetime

noncomputable def ofRestrictPullback
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (hmetric : MetricPullbackTendsto (I := I) Φ)
    (hscalar : ScalarPullbackTendsto (I := I) Φ)
    (hricci : RicciPullbackTendsto (I := I) Φ)
    (hric : RicNormPullback (I := I) Φ)
    (hσsource : forall k : Nat,
      letI : TopologicalSpace (L.atTime 0).M := L.topology
      IsSigmaCompact (Φ.source k))
    (referenceMetric : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      Real -> SmoothRiemannianMetric I (SourceDomain (I := I) Φ k))
    (limitMetricFamily :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      Real -> SmoothRiemannianMetric I L.M)
    (hconv : forall K : Set (L.atTime 0).M,
      forall _hK : letI : TopologicalSpace (L.atTime 0).M := L.topology; IsCompact K,
      forall p : Nat,
      forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
        forall ε : Real, 0 < ε ->
          exists k0 : Nat, forall k : Nat, k0 <= k ->
            forall t : Real, t ∈ Set.Icc a b ->
              ((SourceDomainMetricData.ofRestrictPullback (I := I)
                (Φ := Φ) (k := k) (hσsource k)
                (referenceMetric k) limitMetricFamily).derivNormSupOn (I := I) K p t) < ε) :
    SmoothCGHConverges (I := I) X L subseq :=
  SmoothCGHConverges.ofSpacetime (I := I) Φ hmetric hscalar hricci hric
    (SourceSpacetimeConvergenceData.ofRestrictPullback (I := I)
      hσsource referenceMetric limitMetricFamily hconv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofRestrictPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofRestrictPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofRestrictPullback ``Submission.DifferentialGeometry.CheegerGromovCompactness.SmoothCGHConverges.ofRestrictPullback

end SmoothCGHConverges

end CheegerGromovCompactness
end DifferentialGeometry
