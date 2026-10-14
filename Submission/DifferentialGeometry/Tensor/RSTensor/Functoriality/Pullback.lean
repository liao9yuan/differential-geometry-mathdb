import Submission.DifferentialGeometry.Tensor.RSTensor.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

noncomputable def tensor0SEvalCLM {s : ℕ} {x : M}
    (v : Fin s → TangentSpace I x) :
    Tensor0SSpace s I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A ↦ A v
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SEvalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SEvalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SEvalCLM ``Submission.DifferentialGeometry.tensor0SEvalCLM

@[simp]
theorem tensor0SEvalCLM_apply {s : ℕ} {x : M}
    (v : Fin s → TangentSpace I x) (A : Tensor0SSpace s I x) :
    tensor0SEvalCLM (I := I) (M := M) v A = A v :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SEvalCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SEvalCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SEvalCLM_apply ``Submission.DifferentialGeometry.tensor0SEvalCLM_apply

private noncomputable def tensor0SPullbackValue {s : ℕ} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) : Tensor0SSpace s I x :=
  Tensor0SSpace.ofModel (I := I) (x := x)
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin s ↦ LinearMap.toContinuousLinearMap e.toLinearMap))

run_cmd do
  let target := ``Submission.DifferentialGeometry.tensor0SPullbackValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.tensor0SPullbackValue target :: scope.openDecls } }

private theorem tensor0SPullbackValue_apply {s : ℕ} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) (v : Fin s → TangentSpace I x) :
    tensor0SPullbackValue (I := I) (M := M) e A v = A (fun i ↦ e (v i)) := by
  let _ : T2Space (TangentSpace I x) := by
    change T2Space E
    infer_instance
  change
    ((Tensor0SSpace.toModel A).compContinuousLinearMap
      (fun _ : Fin s ↦ LinearMap.toContinuousLinearMap e.toLinearMap)) v = _
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.tensor0SPullbackValue_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.tensor0SPullbackValue_apply target :: scope.openDecls } }

noncomputable def tensor0SPullbackCLM (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace s I y →L[Real] Tensor0SSpace s I x :=
  LinearMap.toContinuousLinearMap {
    toFun := tensor0SPullbackValue (I := I) (M := M) e
    map_add' := by
      intro A B
      apply tensor0SSpace_ext s x
      intro v
      simp only [tensor0SPullbackValue_apply, Tensor0SSpace.add_apply]
    map_smul' := by
      intro c A
      apply tensor0SSpace_ext s x
      intro v
      simp only [tensor0SPullbackValue_apply, Tensor0SSpace.smul_apply,
        RingHom.id_apply] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SPullbackCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SPullbackCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SPullbackCLM ``Submission.DifferentialGeometry.tensor0SPullbackCLM

@[simp]
theorem tensor0SPullbackCLM_apply (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) (v : Fin s → TangentSpace I x) :
    tensor0SPullbackCLM (I := I) (M := M) s e A v = A (fun i ↦ e (v i)) :=
  tensor0SPullbackValue_apply (I := I) (M := M) e A v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SPullbackCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SPullbackCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SPullbackCLM_apply ``Submission.DifferentialGeometry.tensor0SPullbackCLM_apply

noncomputable def tensor0SPullbackCLE (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace s I y ≃L[Real] Tensor0SSpace s I x where
  toFun := tensor0SPullbackCLM (I := I) (M := M) s e
  invFun := tensor0SPullbackCLM (I := I) (M := M) s e.symm
  left_inv A := by
    apply tensor0SSpace_ext s y
    intro v
    simp
  right_inv A := by
    apply tensor0SSpace_ext s x
    intro v
    simp
  map_add' A B := (tensor0SPullbackCLM (I := I) (M := M) s e).map_add A B
  map_smul' c A := (tensor0SPullbackCLM (I := I) (M := M) s e).map_smul c A
  continuous_toFun := (tensor0SPullbackCLM (I := I) (M := M) s e).continuous
  continuous_invFun := (tensor0SPullbackCLM (I := I) (M := M) s e.symm).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SPullbackCLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SPullbackCLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SPullbackCLE ``Submission.DifferentialGeometry.tensor0SPullbackCLE

@[simp]
theorem tensor0SPullbackCLE_apply (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I y) :
    tensor0SPullbackCLE (I := I) (M := M) s e A =
      tensor0SPullbackCLM (I := I) (M := M) s e A :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SPullbackCLE_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SPullbackCLE_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SPullbackCLE_apply ``Submission.DifferentialGeometry.tensor0SPullbackCLE_apply

@[simp]
theorem tensor0SPullbackCLE_symm_apply (s : ℕ) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace s I x) :
    (tensor0SPullbackCLE (I := I) (M := M) s e).symm A =
      tensor0SPullbackCLM (I := I) (M := M) s e.symm A :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor0SPullbackCLE_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor0SPullbackCLE_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor0SPullbackCLE_symm_apply ``Submission.DifferentialGeometry.tensor0SPullbackCLE_symm_apply

end DifferentialGeometry
