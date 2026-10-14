import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle


open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable {x : M}

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_one_apply_add
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    α (fun _ : Fin 1 => X + Y) =
      α (fun _ : Fin 1 => X) + α (fun _ : Fin 1 => Y) := by
  let base : Fin 1 -> TangentSpace I x := fun _ => 0
  have h := α.map_update_add base (0 : Fin 1) X Y
  have hleft :
      Function.update base (0 : Fin 1) (X + Y) =
        (fun _ : Fin 1 => X + Y) := by
    funext i
    fin_cases i
    simp [base]
  have hX :
      Function.update base (0 : Fin 1) X =
        (fun _ : Fin 1 => X) := by
    funext i
    fin_cases i
    simp [base]
  have hY :
      Function.update base (0 : Fin 1) Y =
        (fun _ : Fin 1 => Y) := by
    funext i
    fin_cases i
    simp [base]
  rw [← hleft, ← hX, ← hY]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0S_one_apply_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.tensor0S_one_apply_add target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private theorem tensor0S_one_apply_smul
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (c : Real) (X : TangentSpace I x) :
    α (fun _ : Fin 1 => c • X) =
      c • α (fun _ : Fin 1 => X) := by
  let base : Fin 1 -> TangentSpace I x := fun _ => 0
  have h := α.map_update_smul base (0 : Fin 1) c X
  have hleft :
      Function.update base (0 : Fin 1) (c • X) =
        (fun _ : Fin 1 => c • X) := by
    funext i
    fin_cases i
    simp [base]
  have hX :
      Function.update base (0 : Fin 1) X =
        (fun _ : Fin 1 => X) := by
    funext i
    fin_cases i
    simp [base]
  rw [← hleft, ← hX]
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0S_one_apply_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.tensor0S_one_apply_smul target :: scope.openDecls } }

private noncomputable def connectionDifferenceSlotCLM
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X : TangentSpace I x) :
    TangentSpace I x →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Y => α (fun _ : Fin 1 => (A Y) X)
      map_add' := by
        intro Y Z
        change α (fun _ : Fin 1 => (A (Y + Z)) X) =
          α (fun _ : Fin 1 => (A Y) X) + α (fun _ : Fin 1 => (A Z) X)
        rw [map_add]
        exact tensor0S_one_apply_add (I := I) α ((A Y) X) ((A Z) X)
      map_smul' := by
        intro c Y
        change α (fun _ : Fin 1 => (A (c • Y)) X) =
          c • α (fun _ : Fin 1 => (A Y) X)
        rw [map_smul]
        exact tensor0S_one_apply_smul (I := I) α c ((A Y) X) }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceSlotCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.connectionDifferenceSlotCLM target :: scope.openDecls } }

noncomputable def connectionDifferenceOutput
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x).symm
    (ContinuousLinearMap.uncurryLeft
      (𝕜 := Real) (n := 1) (Ei := fun _ : Fin 2 => TangentSpace I x) (G := Real)
      (LinearMap.toContinuousLinearMap
        { toFun := fun X =>
            (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
              (connectionDifferenceSlotCLM (I := I) A α X)
          map_add' := by
            intro X Y
            apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
            ext Z
            change α (fun _ : Fin 1 => (A Z) (X + Y)) =
              α (fun _ : Fin 1 => (A Z) X) + α (fun _ : Fin 1 => (A Z) Y)
            rw [map_add]
            exact tensor0S_one_apply_add (I := I) α ((A Z) X) ((A Z) Y)
          map_smul' := by
            intro c X
            apply (continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).injective
            ext Z
            change α (fun _ : Fin 1 => (A Z) (c • X)) =
              c • α (fun _ : Fin 1 => (A Z) X)
            rw [map_smul]
            exact tensor0S_one_apply_smul (I := I) α c ((A Z) X) }))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput

@[simp]
theorem connectionDifferenceOutput_apply
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceOutput (I := I) A α) v =
      Tensor0SSpace.eval α (fun _ : Fin 1 => (A (v 1)) (v 0)) := by
  unfold connectionDifferenceOutput Tensor0SSpace.eval
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.uncurryLeft_apply]
  change
    ((continuousMultilinearCurryFin1 Real (TangentSpace I x) Real).symm
        (connectionDifferenceSlotCLM (I := I) A α (v 0))) (fun i : Fin 1 => v i.succ) =
      α (fun _ : Fin 1 => (A (v 1)) (v 0))
  have htail : (fun i : Fin 1 => v i.succ) = fun _ : Fin 1 => v 1 := by
    funext i
    fin_cases i
    rfl
  rw [htail]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply

theorem connectionDifferenceOutput_apply_slots
    (A :
      TangentSpace I x →L[Real]
        TangentSpace I x →L[Real] TangentSpace I x)
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceOutput (I := I) A α)
        (fun q : Fin 2 => if q = 0 then X else Y) =
      Tensor0SSpace.eval α (fun _ : Fin 1 => (A Y) X) := by
  rw [connectionDifferenceOutput_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply_slots ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceOutput_apply_slots

noncomputable def connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 2 x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        connectionDifferenceOutput (I := I)
          (CovariantDerivative.difference cov cov' x) α
      map_add' := by
        intro α β
        apply tensor0SSpace_ext 2 x
        intro v
        change Tensor0SSpace.eval
            (connectionDifferenceOutput (I := I)
              (CovariantDerivative.difference cov cov' x) (α + β)) v =
          Tensor0SSpace.eval
            (connectionDifferenceOutput (I := I)
                (CovariantDerivative.difference cov cov' x) α +
              connectionDifferenceOutput (I := I)
                (CovariantDerivative.difference cov cov' x) β) v
        rw [connectionDifferenceOutput_apply]
        change Tensor0SSpace.eval (α + β) (fun _ : Fin 1 =>
            (CovariantDerivative.difference cov cov' x (v 1)) (v 0)) = _
        rw [Tensor0SSpace.eval_add]
        rw [Tensor0SSpace.eval_add, connectionDifferenceOutput_apply,
          connectionDifferenceOutput_apply]
      map_smul' := by
        intro c α
        apply tensor0SSpace_ext 2 x
        intro v
        change Tensor0SSpace.eval
            (connectionDifferenceOutput (I := I)
              (CovariantDerivative.difference cov cov' x) (c • α)) v =
          Tensor0SSpace.eval
            (c • connectionDifferenceOutput (I := I)
              (CovariantDerivative.difference cov cov' x) α) v
        rw [Tensor0SSpace.eval_smul, connectionDifferenceOutput_apply]
        change Tensor0SSpace.eval (c • α) (fun _ : Fin 1 =>
            (CovariantDerivative.difference cov cov' x (v 1)) (v 0)) = _
        rw [Tensor0SSpace.eval_smul]
        rw [connectionDifferenceOutput_apply]
        }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt

@[simp]
theorem connectionDifferenceTensorAt_apply
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (v : Fin 2 -> TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceTensorAt (I := I) cov cov' x α) v =
      Tensor0SSpace.eval α (fun _ : Fin 1 =>
        ((CovariantDerivative.difference cov cov' x) (v 1)) (v 0)) := by
  change Tensor0SSpace.eval (connectionDifferenceOutput (I := I)
      (CovariantDerivative.difference cov cov' x) α) v =
    Tensor0SSpace.eval α (fun _ : Fin 1 =>
      ((CovariantDerivative.difference cov cov' x) (v 1)) (v 0))
  rw [connectionDifferenceOutput_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply

theorem connectionDifferenceTensorAt_apply_slots
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M}
    (α : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (X Y : TangentSpace I x) :
    Tensor0SSpace.eval (connectionDifferenceTensorAt (I := I) cov cov' x α)
        (fun q : Fin 2 => if q = 0 then X else Y) =
      Tensor0SSpace.eval α (fun _ : Fin 1 =>
        ((CovariantDerivative.difference cov cov' x) Y) X) := by
  rw [connectionDifferenceTensorAt_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply_slots ``Submission.DifferentialGeometry.Tensor0SBundle.connectionDifferenceTensorAt_apply_slots

theorem componentRS_connectionDifferenceTensorAt
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (i j k : Idx) :
    componentRSField (I := I) basis (connectionDifferenceTensorAt (I := I) cov cov' x)
        (fun _ : Fin 1 => k)
        (fun q : Fin 2 => if q = 0 then i else j) =
      basis.coord k
        (((CovariantDerivative.difference cov cov' x) (basis j)) (basis i)) := by
  classical
  rw [componentRSField_apply]
  change Tensor0SSpace.eval
      (connectionDifferenceTensorAt (I := I) cov cov' x
        (basisTensor0S (I := I) basis fun _ => k))
      (fun a => basis (if a = 0 then i else j)) = _
  rw [connectionDifferenceTensorAt_apply]
  rw [Tensor0SSpace.eval_eq, basisTensor0S_apply]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.componentRS_connectionDifferenceTensorAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.componentRS_connectionDifferenceTensorAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.componentRS_connectionDifferenceTensorAt ``Submission.DifferentialGeometry.Tensor0SBundle.componentRS_connectionDifferenceTensorAt

end Tensor0SBundle
end DifferentialGeometry
