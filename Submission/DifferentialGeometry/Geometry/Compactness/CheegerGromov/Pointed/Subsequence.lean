import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Defs

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

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace PointedRiemannianConvergenceMaps

def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedRiemannianConvergenceMaps (I := I) X L (subseq ∘ φ) where
  partialDiffeomorph k := Φ.partialDiffeomorph (φ k)
  source_exhausts := by
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    exact Φ.source_exhausts.comp_subseq hφ
  base_mem k := Φ.base_mem (φ k)
  basepoint_map k := Φ.basepoint_map (φ k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq

def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L inner) :
    PointedRiemannianConvergenceMaps (I := I) X L (f ∘ inner) where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := Φ.basepoint_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq

def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L id) :
    PointedRiemannianConvergenceMaps (I := I) X L f :=
  Φ.ofSeqSubseq f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
@[simp] theorem compSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat) :
    (Φ.compSubseq φ hφ).source k = Φ.source (φ k) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.compSubseq_source

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
@[simp] theorem ofSeqSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L inner)
    (k : Nat) :
    (Φ.ofSeqSubseq f).source k = Φ.source k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSeqSubseq_source

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
@[simp] theorem ofSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L id)
    (k : Nat) :
    (Φ.ofSubseq f).source k = Φ.source k := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq_source ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConvergenceMaps.ofSubseq_source

end PointedRiemannianConvergenceMaps

namespace MetricSourceData

def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : MetricSourceData (I := I) Φ (φ k)) :
    MetricSourceData (I := I) (Φ.compSubseq φ hφ) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq

def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L inner}
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.ofSeqSubseq f) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq

def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L id}
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.ofSubseq f) k :=
  MetricSourceData.ofSeqSubseq (I := I) f k D

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem compSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : MetricSourceData (I := I) Φ (φ k)) (K : Set L.M) (p : Nat) :
    (MetricSourceData.compSubseq (I := I) φ hφ k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq_supOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq_supOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq_supOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.compSubseq_supOn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ofSeqSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L inner}
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (MetricSourceData.ofSeqSubseq (I := I) f k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq_supOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq_supOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq_supOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSeqSubseq_supOn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ofSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L id}
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (MetricSourceData.ofSubseq (I := I) f k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq_supOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq_supOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq_supOn ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricSourceData.ofSubseq_supOn

end MetricSourceData

namespace MetricConvergenceData

def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (Cd : MetricConvergenceData (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricConvergenceData (I := I) (Φ.compSubseq φ hφ) where
  domain k := MetricSourceData.compSubseq (I := I) φ hφ k (Cd.domain (φ k))
  converges := by
    intro K hK p ε hε
    obtain ⟨k0, hk0⟩ := Cd.converges K hK p ε hε
    exact ⟨k0, fun k hk => hk0 (φ k) (le_trans hk (hφ.id_le k))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.compSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.compSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.compSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.compSubseq

def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L inner}
    (Cd : MetricConvergenceData (I := I) Φ) :
    MetricConvergenceData (I := I) (Φ.ofSeqSubseq f) where
  domain k := MetricSourceData.ofSeqSubseq (I := I) f k (Cd.domain k)
  converges := by
    intro K hK p ε hε
    simpa only [PointedRiemannianConvergenceMaps.ofSeqSubseq_source,
      MetricSourceData.ofSeqSubseq_supOn] using Cd.converges K hK p ε hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSeqSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSeqSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSeqSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSeqSubseq

def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L id}
    (Cd : MetricConvergenceData (I := I) Φ) :
    MetricConvergenceData (I := I) (Φ.ofSubseq f) :=
  Cd.ofSeqSubseq f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricConvergenceData.ofSubseq

end MetricConvergenceData

namespace PointedRiemannianConverges

def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}
    (C : PointedRiemannianConverges (I := I) X L subseq Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedRiemannianConverges (I := I) X L (subseq ∘ φ) (Φ.compSubseq φ hφ) where
  metrics := C.metrics.compSubseq φ hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.compSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.compSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.compSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.compSubseq

def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L inner}
    (C : PointedRiemannianConverges (I := I) (X.subseq f) L inner Φ) :
    PointedRiemannianConverges (I := I) X L (f ∘ inner) (Φ.ofSeqSubseq f) where
  metrics := C.metrics.ofSeqSubseq f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSeqSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSeqSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSeqSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSeqSubseq

def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianConvergenceMaps (I := I) (X.subseq f) L id}
    (C : PointedRiemannianConverges (I := I) (X.subseq f) L id Φ) :
    PointedRiemannianConverges (I := I) X L f (Φ.ofSubseq f) :=
  C.ofSeqSubseq f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.PointedRiemannianConverges.ofSubseq

end PointedRiemannianConverges

namespace MetricCompactLimit

def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (mc : MetricCompactLimit (I := I) (X.subseq f)) :
    MetricCompactLimit (I := I) X where
  subseq := f ∘ mc.subseq
  strictMono := hf.comp mc.strictMono
  limit := mc.limit
  limit_complete := mc.limit_complete
  maps := mc.maps.ofSeqSubseq f
  convergence := mc.convergence.ofSeqSubseq f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ofSeqSubseq_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (mc : MetricCompactLimit (I := I) (X.subseq f)) :
    (mc.ofSeqSubseq f hf).subseq = f ∘ mc.subseq := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_subseq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem ofSeqSubseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (mc : MetricCompactLimit (I := I) (X.subseq f)) :
    (mc.ofSeqSubseq f hf).limit = mc.limit := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_limit ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.ofSeqSubseq_limit

def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactLimit (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricCompactLimit (I := I) X where
  subseq := mc.subseq ∘ φ
  strictMono := mc.strictMono.comp hφ
  limit := mc.limit
  limit_complete := mc.limit_complete
  maps := mc.maps.compSubseq φ hφ
  convergence := mc.convergence.compSubseq φ hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem compSubseq_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactLimit (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    (mc.compSubseq φ hφ).subseq = mc.subseq ∘ φ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_subseq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem compSubseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactLimit (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    (mc.compSubseq φ hφ).limit = mc.limit := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_limit ``Submission.DifferentialGeometry.CheegerGromovCompactness.MetricCompactLimit.compSubseq_limit

end MetricCompactLimit

end CheegerGromovCompactness
end DifferentialGeometry
