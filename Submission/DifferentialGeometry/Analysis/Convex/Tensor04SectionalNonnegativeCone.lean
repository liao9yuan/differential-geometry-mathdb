import Submission.DifferentialGeometry.Analysis.Convex.ProperConeFace
import Submission.DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis.Convex
open _root_.Submission.DifferentialGeometry.Analysis.InnerProductSpace
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

def tensor04SectionalArgs {x : M} (v w : TangentSpace I x) :
    Fin 4 → TangentSpace I x :=
  fun i ↦ if i = 0 then v else if i = 1 then w else if i = 2 then w else v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalArgs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalArgs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalArgs ``Submission.DifferentialGeometry.tensor04SectionalArgs

def tensor04SectionalEval {x : M} (A : Tensor0SSpace 4 I x)
    (v w : TangentSpace I x) : Real :=
  A (tensor04SectionalArgs (I := I) v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalEval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalEval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalEval ``Submission.DifferentialGeometry.tensor04SectionalEval

noncomputable def tensor04SectionalEvalCLM {x : M}
    (v w : TangentSpace I x) : StrongDual Real (Tensor0SSpace 4 I x) :=
  {
    toFun := fun A ↦ tensor04SectionalEval (I := I) (M := M) A v w
    map_add' := by
      intro A B
      rfl
    map_smul' := by
      intro c A
      rfl
    cont := by
      exact (ContinuousMultilinearMap.apply Real
        (fun _ : Fin 4 ↦ TangentSpace I x) Real
        (tensor04SectionalArgs (I := I) v w)).continuous.comp
          (tensor0SSpaceFiberContinuousLinearEquiv
            (I := I) 4 x).continuous }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalEvalCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalEvalCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalEvalCLM ``Submission.DifferentialGeometry.tensor04SectionalEvalCLM

omit [FiniteDimensional Real E] in
@[simp]
theorem tensor04SectionalEvalCLM_apply {x : M}
    (v w : TangentSpace I x) (A : Tensor0SSpace 4 I x) :
    tensor04SectionalEvalCLM (I := I) (M := M) v w A =
      tensor04SectionalEval (I := I) (M := M) A v w :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalEvalCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalEvalCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalEvalCLM_apply ``Submission.DifferentialGeometry.tensor04SectionalEvalCLM_apply

noncomputable def tensor04SectionalNonnegativeCone {x : M} :
    ProperCone Real (Tensor0SSpace 4 I x) :=
  ⨅ v : TangentSpace I x, ⨅ w : TangentSpace I x,
    (ProperCone.positive Real Real).comap
      (tensor04SectionalEvalCLM (I := I) (M := M) v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalNonnegativeCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalNonnegativeCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalNonnegativeCone ``Submission.DifferentialGeometry.tensor04SectionalNonnegativeCone

omit [FiniteDimensional Real E] in
@[simp]
theorem mem_tensor04SectionalNonnegativeCone {x : M}
    {A : Tensor0SSpace 4 I x} :
    A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      ∀ v w : TangentSpace I x,
        0 ≤ tensor04SectionalEval (I := I) (M := M) A v w := by
  simp [tensor04SectionalNonnegativeCone]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mem_tensor04SectionalNonnegativeCone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mem_tensor04SectionalNonnegativeCone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mem_tensor04SectionalNonnegativeCone ``Submission.DifferentialGeometry.mem_tensor04SectionalNonnegativeCone

omit [FiniteDimensional Real E] in
theorem tensor04SectionalEvalCLM_isDualElement {x : M}
    (v w : TangentSpace I x) :
    ProperCone.IsDualElement
      (C := tensor04SectionalNonnegativeCone (I := I) (M := M))
      (tensor04SectionalEvalCLM (I := I) (M := M) v w) := by
  intro A hA
  exact (mem_tensor04SectionalNonnegativeCone.mp hA) v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalEvalCLM_isDualElement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalEvalCLM_isDualElement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalEvalCLM_isDualElement ``Submission.DifferentialGeometry.tensor04SectionalEvalCLM_isDualElement

omit [FiniteDimensional Real E] in
theorem mem_tensor04SectionalNonnegative_dualZeroFace {x : M}
    {A : Tensor0SSpace 4 I x} {v w : TangentSpace I x} :
    A ∈ (tensor04SectionalNonnegativeCone (I := I) (M := M)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) v w) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) ∧
        tensor04SectionalEval (I := I) (M := M) A v w = 0 := by
  simp [ProperCone.mem_dualZeroFace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.mem_tensor04SectionalNonnegative_dualZeroFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.mem_tensor04SectionalNonnegative_dualZeroFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.mem_tensor04SectionalNonnegative_dualZeroFace ``Submission.DifferentialGeometry.mem_tensor04SectionalNonnegative_dualZeroFace

theorem tensor04SectionalEval_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) v w =
      tensor04SectionalEval (I := I) (M := M) A (e v) (e w) := by
  unfold tensor04SectionalEval
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  congr 1
  funext i
  fin_cases i <;> simp [tensor04SectionalArgs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalEval_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalEval_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalEval_pullback ``Submission.DifferentialGeometry.tensor04SectionalEval_pullback

private noncomputable def tensor04SectionalPullbackValue {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) : Tensor0SSpace 4 I x :=
  tensor0SPullbackCLE (I := I) (M := M) 4 e A

run_cmd do
  let target := ``Submission.DifferentialGeometry.tensor04SectionalPullbackValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.tensor04SectionalPullbackValue target :: scope.openDecls } }

private theorem tensor04SectionalPullbackValue_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v : Fin 4 → TangentSpace I x) :
    tensor04SectionalPullbackValue (I := I) (M := M) e A v =
      A (fun i ↦ e (v i)) := by
  unfold tensor04SectionalPullbackValue
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.tensor04SectionalPullbackValue_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.tensor04SectionalPullbackValue_apply target :: scope.openDecls } }

private noncomputable def tensor04SectionalPullbackCLM {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 4 I y →L[Real] Tensor0SSpace 4 I x where
  toFun := tensor04SectionalPullbackValue (I := I) (M := M) e
  map_add' A B := by
    apply tensor0SSpace_ext 4 x
    intro v
    change (A + B) (fun i ↦ e (v i)) =
      A (fun i ↦ e (v i)) + B (fun i ↦ e (v i))
    rfl
  map_smul' c A := by
    apply tensor0SSpace_ext 4 x
    intro v
    change (c • A) (fun i ↦ e (v i)) = c • A (fun i ↦ e (v i))
    rfl
  cont := by
    change Continuous (fun A : Tensor0SSpace 4 I y =>
      tensor0SPullbackCLE (I := I) (M := M) 4 e A)
    exact (tensor0SPullbackCLE (I := I) (M := M) 4 e).continuous_toFun

run_cmd do
  let target := ``Submission.DifferentialGeometry.tensor04SectionalPullbackCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.tensor04SectionalPullbackCLM target :: scope.openDecls } }

noncomputable def tensor04SectionalPullbackCLE {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    Tensor0SSpace 4 I y ≃L[Real] Tensor0SSpace 4 I x where
  toFun := tensor04SectionalPullbackCLM (I := I) (M := M) e
  invFun := tensor04SectionalPullbackCLM (I := I) (M := M) e.symm
  left_inv A := by
    apply tensor0SSpace_ext 4 y
    intro v
    change A (fun i ↦ e (e.symm (v i))) = A v
    congr 1
    funext i
    simp
  right_inv A := by
    apply tensor0SSpace_ext 4 x
    intro v
    change A (fun i ↦ e.symm (e (v i))) = A v
    congr 1
    funext i
    simp
  map_add' A B := (tensor04SectionalPullbackCLM (I := I) (M := M) e).map_add A B
  map_smul' c A := (tensor04SectionalPullbackCLM (I := I) (M := M) e).map_smul c A
  continuous_toFun := (tensor04SectionalPullbackCLM (I := I) (M := M) e).continuous
  continuous_invFun := (tensor04SectionalPullbackCLM (I := I) (M := M) e.symm).continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalPullbackCLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalPullbackCLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalPullbackCLE ``Submission.DifferentialGeometry.tensor04SectionalPullbackCLE

@[simp]
theorem tensor04SectionalPullbackCLE_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v : Fin 4 → TangentSpace I x) :
    tensor04SectionalPullbackCLE (I := I) (M := M) e A v =
      A (fun i ↦ e (v i)) :=
  tensor04SectionalPullbackValue_apply (I := I) (M := M) e A v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalPullbackCLE_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalPullbackCLE_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalPullbackCLE_apply ``Submission.DifferentialGeometry.tensor04SectionalPullbackCLE_apply

theorem tensor04SectionalEval_normPullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) (v w : TangentSpace I x) :
    tensor04SectionalEval (I := I) (M := M)
        (tensor04SectionalPullbackCLE (I := I) (M := M) e A) v w =
      tensor04SectionalEval (I := I) (M := M) A (e v) (e w) := by
  unfold tensor04SectionalEval
  rw [tensor04SectionalPullbackCLE_apply]
  congr 1
  funext i
  fin_cases i <;> simp [tensor04SectionalArgs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalEval_normPullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalEval_normPullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalEval_normPullback ``Submission.DifferentialGeometry.tensor04SectionalEval_normPullback

theorem tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace 4 I y) :
    tensor04SectionalPullbackCLE (I := I) (M := M) e A ∈
        tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
      A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M) := by
  constructor
  · intro hA
    apply mem_tensor04SectionalNonnegativeCone.mpr
    intro v w
    have h := mem_tensor04SectionalNonnegativeCone.mp hA (e.symm v) (e.symm w)
    rw [tensor04SectionalEval_normPullback] at h
    simpa using h
  · intro hA
    apply mem_tensor04SectionalNonnegativeCone.mpr
    intro v w
    rw [tensor04SectionalEval_normPullback]
    exact mem_tensor04SectionalNonnegativeCone.mp hA (e v) (e w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff ``Submission.DifferentialGeometry.tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff

theorem tensor04SectionalNonnegativeCone_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 4 I y)).map
        (tensor04SectionalPullbackCLE (I := I) (M := M) e).toContinuousLinearMap =
      (tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 4 I x)) := by
  apply ProperCone.ext
  intro A
  rw [ProperCone.mem_map_continuousLinearEquiv_iff]
  change tensor04SectionalPullbackCLE (I := I) (M := M) e.symm A ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M) ↔
    A ∈ tensor04SectionalNonnegativeCone (I := I) (M := M)
  exact tensor04SectionalPullbackCLE_mem_sectionalNonnegativeCone_iff
    (I := I) (M := M) e.symm A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalNonnegativeCone_map_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalNonnegativeCone_map_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalNonnegativeCone_map_pullback ``Submission.DifferentialGeometry.tensor04SectionalNonnegativeCone_map_pullback

theorem tensor04SectionalNonnegative_dualZeroFace_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (v w : TangentSpace I x) :
    ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
      ProperCone Real (Tensor0SSpace 4 I y)).dualZeroFace
        (tensor04SectionalEvalCLM (I := I) (M := M) (e v) (e w))).map
          (tensor04SectionalPullbackCLE (I := I) (M := M) e).toContinuousLinearMap =
      ((tensor04SectionalNonnegativeCone (I := I) (M := M) :
        ProperCone Real (Tensor0SSpace 4 I x)).dualZeroFace
          (tensor04SectionalEvalCLM (I := I) (M := M) v w)) := by
  rw [ProperCone.dualZeroFace_map_continuousLinearEquiv]
  rw [tensor04SectionalNonnegativeCone_map_pullback]
  congr 1
  apply ContinuousLinearMap.ext
  intro A
  change tensor04SectionalEval (I := I) (M := M)
      ((tensor04SectionalPullbackCLE (I := I) (M := M) e).symm A) (e v) (e w) =
    tensor04SectionalEval (I := I) (M := M) A v w
  change tensor04SectionalEval (I := I) (M := M)
      (tensor04SectionalPullbackCLE (I := I) (M := M) e.symm A) (e v) (e w) = _
  rw [tensor04SectionalEval_normPullback]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.tensor04SectionalNonnegative_dualZeroFace_map_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.tensor04SectionalNonnegative_dualZeroFace_map_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.tensor04SectionalNonnegative_dualZeroFace_map_pullback ``Submission.DifferentialGeometry.tensor04SectionalNonnegative_dualZeroFace_map_pullback

end DifferentialGeometry
