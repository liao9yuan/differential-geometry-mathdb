import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev Circle := AddCircle (1 : ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Circle


abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere


abbrev ContinuousFreeLoop (Q : Type*) [TopologicalSpace Q] := C(Circle, Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContinuousFreeLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContinuousFreeLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContinuousFreeLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContinuousFreeLoop


abbrev SphereFamily (Q : Type*) [TopologicalSpace Q] := C(Sphere 2, ContinuousFreeLoop Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphereFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphereFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphereFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SphereFamily

variable {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R]


def loopEvaluation : C(ContinuousFreeLoop Q, Q) :=
  ⟨fun γ => γ 0, _root_.ContinuousEvalConst.continuous_eval_const 0⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation


def constantLoops : C(Q, ContinuousFreeLoop Q) := ContinuousMap.const'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.constantLoops then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.constantLoops"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.constantLoops ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.constantLoops

@[simp] theorem loopEvaluation_constantLoops (q : Q) :
    loopEvaluation (constantLoops q) = q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation_constantLoops then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation_constantLoops"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation_constantLoops ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopEvaluation_constantLoops


abbrev BasedContinuousLoop (q : Q) := {γ : ContinuousFreeLoop Q // γ 0 = q}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BasedContinuousLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BasedContinuousLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BasedContinuousLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BasedContinuousLoop


def basedConstantLoop (q : Q) : BasedContinuousLoop q := ⟨constantLoops q, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedConstantLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedConstantLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedConstantLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedConstantLoop


def basedLoopInclusion (q : Q) : C(BasedContinuousLoop q, ContinuousFreeLoop Q) :=
  ⟨Subtype.val, continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedLoopInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedLoopInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedLoopInclusion ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.basedLoopInclusion


def loopPostcompose (f : C(P, Q)) : C(ContinuousFreeLoop P, ContinuousFreeLoop Q) :=
  ⟨fun γ => f.comp γ, ContinuousMap.continuous_postcomp f⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose

@[simp] theorem loopPostcompose_apply (f : C(P, Q)) (γ : ContinuousFreeLoop P)
    (z : Circle) : loopPostcompose f γ z = f (γ z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_apply

@[simp] theorem loopPostcompose_constantLoops (f : C(P, Q)) (p : P) :
    loopPostcompose f (constantLoops p) = constantLoops (f p) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_constantLoops then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_constantLoops"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_constantLoops ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_constantLoops

@[simp] theorem loopPostcompose_id :
    loopPostcompose (ContinuousMap.id Q) = ContinuousMap.id (ContinuousFreeLoop Q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_id ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_id

@[simp] theorem loopPostcompose_comp (f : C(P, Q)) (g : C(Q, R)) :
    loopPostcompose (g.comp f) = (loopPostcompose g).comp (loopPostcompose f) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_comp ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.loopPostcompose_comp


def IsContractibleLoop (γ : ContinuousFreeLoop Q) : Prop :=
  ∃ q : Q, ContinuousMap.Homotopic γ (constantLoops q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop


abbrev ContractibleContinuousLoop (Q : Type*) [TopologicalSpace Q] :=
  {γ : ContinuousFreeLoop Q // IsContractibleLoop γ}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleContinuousLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleContinuousLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleContinuousLoop ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleContinuousLoop


abbrev ContractibleSphereFamily (Q : Type*) [TopologicalSpace Q] :=
  C(Sphere 2, ContractibleContinuousLoop Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleSphereFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleSphereFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleSphereFamily ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ContractibleSphereFamily

theorem isContractibleLoop_constant (q : Q) : IsContractibleLoop (constantLoops q) :=
  ⟨q, ContinuousMap.Homotopic.refl _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isContractibleLoop_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isContractibleLoop_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isContractibleLoop_constant ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isContractibleLoop_constant

theorem IsContractibleLoop.postcompose {γ : ContinuousFreeLoop P}
    (hγ : IsContractibleLoop γ) (f : C(P, Q)) :
    IsContractibleLoop (loopPostcompose f γ) := by
  obtain ⟨p, hp⟩ := hγ
  exact ⟨f p, (ContinuousMap.Homotopic.refl f).comp hp⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop.postcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop.postcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop.postcompose ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IsContractibleLoop.postcompose


def contractibleLoopPostcompose (f : C(P, Q)) :
    C(ContractibleContinuousLoop P, ContractibleContinuousLoop Q) :=
  ⟨fun γ => ⟨loopPostcompose f γ.1, γ.2.postcompose f⟩,
    ((loopPostcompose f).continuous.comp continuous_subtype_val).subtype_mk _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contractibleLoopPostcompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contractibleLoopPostcompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contractibleLoopPostcompose ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.contractibleLoopPostcompose


def freeHomotopySetoid (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Setoid C(X, Y) := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.freeHomotopySetoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.freeHomotopySetoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.freeHomotopySetoid ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.freeHomotopySetoid


def FreeHomotopyClass (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  Quotient (freeHomotopySetoid X Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass


abbrev FreeSphereClass (Q : Type*) [TopologicalSpace Q] :=
  FreeHomotopyClass (Sphere 2) (ContinuousFreeLoop Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeSphereClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeSphereClass


abbrev FreeContractibleSphereClass (Q : Type*) [TopologicalSpace Q] :=
  FreeHomotopyClass (Sphere 2) (ContractibleContinuousLoop Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeContractibleSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeContractibleSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeContractibleSphereClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeContractibleSphereClass

namespace FreeHomotopyClass

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


def mk (f : C(X, Y)) : FreeHomotopyClass X Y := Quotient.mk _ f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk

theorem mk_eq_mk_iff (f g : C(X, Y)) : mk f = mk g ↔ ContinuousMap.Homotopic f g :=
  Quotient.eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk_eq_mk_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk_eq_mk_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk_eq_mk_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.mk_eq_mk_iff


def map (f : C(Y, Z)) : FreeHomotopyClass X Y → FreeHomotopyClass X Z :=
  Quotient.map (fun g => f.comp g)
    (fun _ _ h => (ContinuousMap.Homotopic.refl f).comp h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map

@[simp] theorem map_mk (f : C(Y, Z)) (g : C(X, Y)) : map f (mk g) = mk (f.comp g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_mk ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_mk

@[simp] theorem map_id (ξ : FreeHomotopyClass X Y) : map (ContinuousMap.id Y) ξ = ξ := by
  induction ξ using Quotient.inductionOn with
  | h f => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_id ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_id

@[simp] theorem map_comp {W : Type*} [TopologicalSpace W]
    (f : C(Y, Z)) (g : C(Z, W)) (ξ : FreeHomotopyClass X Y) :
    map (g.comp f) ξ = map g (map f ξ) := by
  induction ξ using Quotient.inductionOn with
  | h h => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_comp ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FreeHomotopyClass.map_comp

end FreeHomotopyClass


def sphereFamilyUncurry (Γ : SphereFamily Q) : C(Sphere 2 × Circle, Q) := Γ.uncurry

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry

@[simp] theorem sphereFamilyUncurry_apply (Γ : SphereFamily Q) (p : Sphere 2) (z : Circle) :
    sphereFamilyUncurry Γ (p, z) = Γ p z := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.sphereFamilyUncurry_apply

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ThreeSpace

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
