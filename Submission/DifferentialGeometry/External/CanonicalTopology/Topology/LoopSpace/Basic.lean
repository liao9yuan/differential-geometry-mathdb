import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Instances.AddCircle.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Parametrized continuous loops

The circle is `ℝ / ℤ`, and the loop topology is the compact-open topology.
This supplies the continuous objects of `def:rfs-continuous-loop-model`
and `def:rfs-regular-loops`. No regularity, immersion, or reparametrization
quotient is imposed here. The evaluation fibration and the signed homotopy
group identification are separate, still missing theorems.
-/

noncomputable section

open _root_.ContinuousMap

namespace DifferentialGeometry.Topology

/-- The period-one parameter circle. -/
abbrev loopCircle := UnitAddCircle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.loopCircle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.loopCircle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.loopCircle ``Submission.DifferentialGeometry.Topology.loopCircle

/-- Parametrized continuous loops, with Mathlib's compact-open topology. -/
abbrev freeLoop (Q : Type*) [TopologicalSpace Q] := C(loopCircle, Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.freeLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.freeLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.freeLoop ``Submission.DifferentialGeometry.Topology.freeLoop

/-- The subspace of nullhomotopic parametrized continuous loops. -/
abbrev contractibleLoop (Q : Type*) [TopologicalSpace Q] :=
  {γ : freeLoop Q // γ.Nullhomotopic}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.contractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.contractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.contractibleLoop ``Submission.DifferentialGeometry.Topology.contractibleLoop

/-- The exponential law identifies free homotopies with paths in mapping space. -/
theorem homotopic_iff_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] (f g : C(X, Y)) : f.Homotopic g ↔ Joined f g := by
  constructor
  · rintro ⟨H⟩
    exact ⟨⟨H.curry, H.curry_zero, H.curry_one⟩⟩
  · rintro ⟨p⟩
    exact ⟨⟨p.toContinuousMap.uncurry,
      fun x => congrArg (fun h : C(X, Y) => h x) p.source,
      fun x => congrArg (fun h : C(X, Y) => h x) p.target⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.homotopic_iff_joined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.homotopic_iff_joined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.homotopic_iff_joined ``Submission.DifferentialGeometry.Topology.homotopic_iff_joined

namespace FreeLoop

variable {P Q R K : Type*}
  [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R] [TopologicalSpace K]

/-- Evaluation at the specified parameter zero. -/
def evaluation : C(freeLoop Q, Q) := ⟨fun γ => γ 0, _root_.ContinuousEvalConst.continuous_eval_const 0⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.evaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.evaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.evaluation ``Submission.DifferentialGeometry.Topology.FreeLoop.evaluation

/-- The continuous section consisting of constant loops. -/
def constants : C(Q, freeLoop Q) := ContinuousMap.const'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.constants ``Submission.DifferentialGeometry.Topology.FreeLoop.constants

@[simp] theorem evaluation_apply (γ : freeLoop Q) : evaluation γ = γ 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.evaluation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.evaluation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.evaluation_apply ``Submission.DifferentialGeometry.Topology.FreeLoop.evaluation_apply

@[simp] theorem constants_apply (q : Q) (θ : loopCircle) : constants q θ = q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.constants_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.constants_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.constants_apply ``Submission.DifferentialGeometry.Topology.FreeLoop.constants_apply

@[simp] theorem evaluation_constants : (evaluation (Q := Q)).comp constants = .id Q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.evaluation_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.evaluation_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.evaluation_constants ``Submission.DifferentialGeometry.Topology.FreeLoop.evaluation_constants

/-- Postcomposition needs only continuity of the target map. -/
def postcompose (f : C(P, Q)) : C(freeLoop P, freeLoop Q) :=
  ⟨ContinuousMap.comp f, _root_.ContinuousMap.continuous_postcomp f⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.postcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.postcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.postcompose ``Submission.DifferentialGeometry.Topology.FreeLoop.postcompose

@[simp] theorem postcompose_apply (f : C(P, Q)) (γ : freeLoop P) (θ : loopCircle) :
    postcompose f γ θ = f (γ θ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.postcompose_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.postcompose_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.postcompose_apply ``Submission.DifferentialGeometry.Topology.FreeLoop.postcompose_apply

@[simp] theorem postcompose_id : postcompose (.id Q) = .id (freeLoop Q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.postcompose_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.postcompose_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.postcompose_id ``Submission.DifferentialGeometry.Topology.FreeLoop.postcompose_id

@[simp] theorem postcompose_comp (g : C(Q, R)) (f : C(P, Q)) :
    postcompose (g.comp f) = (postcompose g).comp (postcompose f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.postcompose_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.postcompose_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.postcompose_comp ``Submission.DifferentialGeometry.Topology.FreeLoop.postcompose_comp

theorem evaluation_postcompose (f : C(P, Q)) :
    evaluation.comp (postcompose f) = f.comp evaluation := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.evaluation_postcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.evaluation_postcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.evaluation_postcompose ``Submission.DifferentialGeometry.Topology.FreeLoop.evaluation_postcompose

theorem postcompose_constants (f : C(P, Q)) :
    (postcompose f).comp constants = constants.comp f := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.postcompose_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.postcompose_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.postcompose_constants ``Submission.DifferentialGeometry.Topology.FreeLoop.postcompose_constants

/-- A continuous family has a jointly continuous adjoint, without any condition on `K`. -/
def adjoint (Γ : C(K, freeLoop Q)) : C(K × loopCircle, Q) := Γ.uncurry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.adjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.adjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.adjoint ``Submission.DifferentialGeometry.Topology.FreeLoop.adjoint

@[simp] theorem adjoint_apply (Γ : C(K, freeLoop Q)) (k : K) (θ : loopCircle) :
    adjoint Γ (k, θ) = Γ k θ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.adjoint_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.adjoint_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.adjoint_apply ``Submission.DifferentialGeometry.Topology.FreeLoop.adjoint_apply

theorem continuous_family_iff (Γ : K → freeLoop Q) :
    Continuous Γ ↔ Continuous (fun p : K × loopCircle => Γ p.1 p.2) := by
  constructor
  · intro h
    exact (adjoint ⟨Γ, h⟩).continuous
  · exact _root_.ContinuousMap.continuous_of_continuous_uncurry Γ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.continuous_family_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.continuous_family_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.continuous_family_iff ``Submission.DifferentialGeometry.Topology.FreeLoop.continuous_family_iff

/-- The exponential law identifies free homotopies of loops with paths in loop space. -/
theorem homotopic_iff_joined (γ η : freeLoop Q) : γ.Homotopic η ↔ Joined γ η := by
  exact DifferentialGeometry.Topology.homotopic_iff_joined γ η

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.homotopic_iff_joined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.homotopic_iff_joined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.homotopic_iff_joined ``Submission.DifferentialGeometry.Topology.FreeLoop.homotopic_iff_joined

/-- Contractibility is preserved throughout any free homotopy. -/
theorem nullhomotopic_of_homotopic {γ η : freeLoop Q} (h : γ.Homotopic η)
    (hγ : γ.Nullhomotopic) : η.Nullhomotopic := by
  obtain ⟨q, hq⟩ := hγ
  exact ⟨q, h.symm.trans hq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FreeLoop.nullhomotopic_of_homotopic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FreeLoop.nullhomotopic_of_homotopic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FreeLoop.nullhomotopic_of_homotopic ``Submission.DifferentialGeometry.Topology.FreeLoop.nullhomotopic_of_homotopic

end FreeLoop

namespace ContractibleLoop

variable {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R]

/-- Inclusion of the contractible-loop subspace into the full loop space. -/
def inclusion : C(contractibleLoop Q, freeLoop Q) := ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.inclusion ``Submission.DifferentialGeometry.Topology.ContractibleLoop.inclusion

/-- Constant loops belong to the contractible-loop subspace, continuously in their value. -/
def constants : C(Q, contractibleLoop Q) :=
  ⟨fun q => ⟨.const loopCircle q, _root_.ContinuousMap.nullhomotopic_of_constant q⟩,
    continuous_const'.subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.constants ``Submission.DifferentialGeometry.Topology.ContractibleLoop.constants

/-- Evaluation on contractible loops. -/
def evaluation : C(contractibleLoop Q, Q) := FreeLoop.evaluation.comp inclusion

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.evaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.evaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.evaluation ``Submission.DifferentialGeometry.Topology.ContractibleLoop.evaluation

@[simp] theorem constants_apply (q : Q) (θ : loopCircle) : (constants q).val θ = q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.constants_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.constants_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.constants_apply ``Submission.DifferentialGeometry.Topology.ContractibleLoop.constants_apply

@[simp] theorem evaluation_constants : (evaluation (Q := Q)).comp constants = .id Q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.evaluation_constants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.evaluation_constants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.evaluation_constants ``Submission.DifferentialGeometry.Topology.ContractibleLoop.evaluation_constants

/-- Continuous maps preserve loop contractions by composing the actual homotopy. -/
def postcompose (f : C(P, Q)) : C(contractibleLoop P, contractibleLoop Q) :=
  ⟨fun γ => ⟨f.comp γ.val, γ.property.comp_right f⟩,
    ((_root_.ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.postcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.postcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.postcompose ``Submission.DifferentialGeometry.Topology.ContractibleLoop.postcompose

@[simp] theorem postcompose_apply (f : C(P, Q)) (γ : contractibleLoop P) (θ : loopCircle) :
    (postcompose f γ).val θ = f (γ.val θ) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.postcompose_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.postcompose_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.postcompose_apply ``Submission.DifferentialGeometry.Topology.ContractibleLoop.postcompose_apply

@[simp] theorem postcompose_id : postcompose (.id Q) = .id (contractibleLoop Q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.postcompose_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.postcompose_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.postcompose_id ``Submission.DifferentialGeometry.Topology.ContractibleLoop.postcompose_id

@[simp] theorem postcompose_comp (g : C(Q, R)) (f : C(P, Q)) :
    postcompose (g.comp f) = (postcompose g).comp (postcompose f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.postcompose_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.postcompose_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.postcompose_comp ``Submission.DifferentialGeometry.Topology.ContractibleLoop.postcompose_comp

theorem inclusion_postcompose (f : C(P, Q)) :
    inclusion.comp (postcompose f) = (FreeLoop.postcompose f).comp inclusion := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ContractibleLoop.inclusion_postcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ContractibleLoop.inclusion_postcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ContractibleLoop.inclusion_postcompose ``Submission.DifferentialGeometry.Topology.ContractibleLoop.inclusion_postcompose

end ContractibleLoop

end DifferentialGeometry.Topology
