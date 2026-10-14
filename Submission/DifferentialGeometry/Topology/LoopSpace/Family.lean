import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission










noncomputable section

open _root_.ContinuousMap

namespace DifferentialGeometry.Topology


abbrev familySphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.familySphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.familySphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.familySphere ``Submission.DifferentialGeometry.Topology.familySphere


abbrev loopFamilyClass (Q : Type*) [TopologicalSpace Q] :=
  ZerothHomotopy C(familySphere, contractibleLoop Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopFamilyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopFamilyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopFamilyClass ``Submission.DifferentialGeometry.Topology.loopFamilyClass

namespace LoopFamily

variable {P Q R K : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace R] [TopologicalSpace K]


def classOf (Γ : C(familySphere, contractibleLoop Q)) : loopFamilyClass Q := .mk Γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.classOf ``Submission.DifferentialGeometry.Topology.LoopFamily.classOf


theorem classOf_eq_iff (Γ Δ : C(familySphere, contractibleLoop Q)) :
    classOf Γ = classOf Δ ↔ Γ.Homotopic Δ := by
  change Quotient.mk _ Γ = Quotient.mk _ Δ ↔ _
  rw [Quotient.eq]
  exact (DifferentialGeometry.Topology.homotopic_iff_joined Γ Δ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.classOf_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.classOf_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.classOf_eq_iff ``Submission.DifferentialGeometry.Topology.LoopFamily.classOf_eq_iff



theorem exists_representative (ξ : loopFamilyClass Q) :
    ∃ Γ : C(familySphere, contractibleLoop Q), classOf Γ = ξ :=
  ZerothHomotopy.mk_surjective ξ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.exists_representative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.exists_representative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.exists_representative ``Submission.DifferentialGeometry.Topology.LoopFamily.exists_representative


def postcompose (f : C(P, Q)) : loopFamilyClass P → loopFamilyClass Q :=
  ZerothHomotopy.lift (fun Γ => classOf ((ContractibleLoop.postcompose f).comp Γ))
    (fun {_ _} p => ZerothHomotopy.sound (p.map (_root_.ContinuousMap.continuous_postcomp (ContractibleLoop.postcompose f))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.postcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.postcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.postcompose ``Submission.DifferentialGeometry.Topology.LoopFamily.postcompose

@[simp] theorem postcompose_classOf (f : C(P, Q)) (Γ : C(familySphere, contractibleLoop P)) :
    postcompose f (classOf Γ) = classOf ((ContractibleLoop.postcompose f).comp Γ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.postcompose_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.postcompose_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.postcompose_classOf ``Submission.DifferentialGeometry.Topology.LoopFamily.postcompose_classOf

@[simp] theorem postcompose_id (ξ : loopFamilyClass Q) : postcompose (.id Q) ξ = ξ := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.postcompose_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.postcompose_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.postcompose_id ``Submission.DifferentialGeometry.Topology.LoopFamily.postcompose_id

theorem postcompose_comp (g : C(Q, R)) (f : C(P, Q)) (ξ : loopFamilyClass P) :
    postcompose (g.comp f) ξ = postcompose g (postcompose f ξ) := by
  induction ξ using ZerothHomotopy.rec with
  | mk Γ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.postcompose_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.postcompose_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.postcompose_comp ``Submission.DifferentialGeometry.Topology.LoopFamily.postcompose_comp


def constants (f : C(K, Q)) : C(K, contractibleLoop Q) := ContractibleLoop.constants.comp f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.constants ``Submission.DifferentialGeometry.Topology.LoopFamily.constants




theorem constants_nullhomotopic_iff (f : C(K, Q)) : (constants f).Nullhomotopic ↔ f.Nullhomotopic := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨ContractibleLoop.evaluation γ,
      (ContinuousMap.Homotopic.refl ContractibleLoop.evaluation).comp hγ⟩
  · exact fun hf => hf.comp_right ContractibleLoop.constants

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.constants_nullhomotopic_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.constants_nullhomotopic_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.constants_nullhomotopic_iff ``Submission.DifferentialGeometry.Topology.LoopFamily.constants_nullhomotopic_iff


def nullClass (q : Q) : loopFamilyClass Q :=
  classOf (.const familySphere (ContractibleLoop.constants q))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.nullClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.nullClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.nullClass ``Submission.DifferentialGeometry.Topology.LoopFamily.nullClass

@[simp] theorem postcompose_nullClass (f : C(P, Q)) (p : P) :
    postcompose f (nullClass p) = nullClass (f p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.postcompose_nullClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.postcompose_nullClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.postcompose_nullClass ``Submission.DifferentialGeometry.Topology.LoopFamily.postcompose_nullClass


theorem nullClass_eq [PathConnectedSpace Q] (q r : Q) : nullClass q = nullClass r := by
  apply (classOf_eq_iff _ _).mpr
  exact ⟨((PathConnectedSpace.somePath q r).map ContractibleLoop.constants.continuous).toHomotopyConst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.LoopFamily.nullClass_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.LoopFamily.nullClass_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.LoopFamily.nullClass_eq ``Submission.DifferentialGeometry.Topology.LoopFamily.nullClass_eq

end LoopFamily

end DifferentialGeometry.Topology
