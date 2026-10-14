import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCovering.Sequence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open _root_.Set
open scoped _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

noncomputable def seqCenterD
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat) : (X.obj (L.φ k)).M :=
  (seqCenter hd D P (L.φ k) gamma).getD (X.obj (L.φ k)).basepoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.seqCenterD then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.seqCenterD"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.seqCenterD ``Submission.DifferentialGeometry.CheegerGromovCompactness.seqCenterD

omit [CompleteSpace E] in
theorem seqCenterD_dist_eq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    seqRadius hd D P (L.φ k) gamma =
      dist (seqCenterD hd P L k gamma) (X.obj (L.φ k)).basepoint := by
  let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  have : ProperSpace (X.obj (L.φ k)).M := (P (L.φ k)).proper
  unfold seqRadius seqCenterD seqCenter OrderedNet.netRadius
  cases OrderedNet.netCenter (X.obj (L.φ k)).basepoint (hd.lambda D)
      (hd.lambda_continuous D) gamma <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_dist_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.seqCenterD_dist_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_dist_eq ``Submission.DifferentialGeometry.CheegerGromovCompactness.seqCenterD_dist_eq

omit [CompleteSpace E] in
@[simp] theorem seqCenterD_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) {ψ : Nat → Nat} (hψ : StrictMono ψ)
    (k gamma : Nat) :
    seqCenterD hd P (L.subseq hψ) k gamma = seqCenterD hd P L (ψ k) gamma := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_subseq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.seqCenterD_subseq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_subseq ``Submission.DifferentialGeometry.CheegerGromovCompactness.seqCenterD_subseq

def LiveSlot
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :=
  {gamma : Fin (pb.A r) // L.alive (gamma : Nat) = _root_.Bool.true}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.LiveSlot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.LiveSlot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.LiveSlot ``Submission.DifferentialGeometry.CheegerGromovCompactness.LiveSlot

noncomputable instance liveSlotFintype
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    {P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)}
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    Fintype (LiveSlot L pb r) := by
  letI : Finite (LiveSlot L pb r) :=
    Finite.of_injective (fun gamma : LiveSlot L pb r => gamma.1)
      Subtype.val_injective
  exact Fintype.ofFinite (LiveSlot L pb r)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.liveSlotFintype then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.liveSlotFintype"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.liveSlotFintype ``Submission.DifferentialGeometry.CheegerGromovCompactness.liveSlotFintype

omit [CompleteSpace E] in
theorem seqCenterD_some
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (k gamma : Nat)
    (h : (seqCenter hd D P (L.φ k) gamma).isSome = _root_.Bool.true) :
    seqCenter hd D P (L.φ k) gamma = _root_.Option.some (seqCenterD hd P L k gamma) := by
  cases hc : seqCenter hd D P (L.φ k) gamma with
  | none => simp [hc] at h
  | some c => simp [seqCenterD, hc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_some then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.seqCenterD_some"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_some ``Submission.DifferentialGeometry.CheegerGromovCompactness.seqCenterD_some

omit [CompleteSpace E] in
theorem seqCenterD_live
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) (hgamma : L.alive gamma = _root_.Bool.true) :
    ∀ᶠ k in Filter.atTop,
      seqCenter hd D P (L.φ k) gamma = _root_.Option.some (seqCenterD hd P L k gamma) :=
  (L.alive_eventually gamma).mono fun k hk =>
    seqCenterD_some hd P L k gamma (hk.trans hgamma)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_live then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.seqCenterD_live"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.seqCenterD_live ``Submission.DifferentialGeometry.CheegerGromovCompactness.seqCenterD_live

omit [CompleteSpace E] in
theorem seqCenter_dead
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (gamma : Nat) (hgamma : L.alive gamma = _root_.Bool.false) :
    ∀ᶠ k in Filter.atTop, seqCenter hd D P (L.φ k) gamma = none :=
  (L.alive_eventually gamma).mono fun k hk => by
    cases hc : seqCenter hd D P (L.φ k) gamma with
    | none => rfl
    | some c => simp [hc, hgamma] at hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.seqCenter_dead then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.seqCenter_dead"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.seqCenter_dead ``Submission.DifferentialGeometry.CheegerGromovCompactness.seqCenter_dead

end CheegerGromovCompactness
end DifferentialGeometry
