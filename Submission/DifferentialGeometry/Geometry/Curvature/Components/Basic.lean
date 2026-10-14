import Submission.DifferentialGeometry.Geometry.Curvature.Sections.Connection
import Submission.DifferentialGeometry.Geometry.Connection.RicciIdentity.OneForm.Realization
import Submission.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Realization
import Submission.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Formula
import Submission.DifferentialGeometry.Geometry.Connection.RicciIdentity.MixedComponents
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import Submission.DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

def slots2 (i j : Idx) : Fin 2 -> Idx :=
  fun a => if a = 0 then i else j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.slots2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.slots2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.slots2 ``Submission.DifferentialGeometry.Geometry.Curvature.slots2


def slots4 (i j k l : Idx) : Fin 4 -> Idx :=
  fun a => if a = 0 then i else if a = 1 then j else if a = 2 then k else l

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.slots4 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.slots4"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.slots4 ``Submission.DifferentialGeometry.Geometry.Curvature.slots4


def ricciCompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) : Real :=
  component0S (I := I) basis Ric (slots2 i j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciCompAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciCompAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciCompAt ``Submission.DifferentialGeometry.Geometry.Curvature.ricciCompAt


def rm04CompAt
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) : Real :=
  component0S (I := I) basis Rm04 (slots4 i j k l)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04CompAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04CompAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04CompAt ``Submission.DifferentialGeometry.Geometry.Curvature.rm04CompAt

omit [FiniteDimensional ℝ E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem ricciCompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Ric : Tensor02At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis Ric i j =
      Ric (vec2 (basis i) (basis j)) := by
  unfold ricciCompAt component0S slots2 vec2
  congr 1
  funext a
  fin_cases a <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply

omit [FiniteDimensional ℝ E] [Fintype Idx] [DecidableEq Idx] in
@[simp]
theorem rm04CompAt_apply
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm04 : Tensor04At (I := I) (M := M) x) (i j k l : Idx) :
    rm04CompAt (I := I) basis Rm04 i j k l =
      Rm04 (vec4 (basis i) (basis j) (basis k) (basis l)) := by
  unfold rm04CompAt component0S slots4 vec4
  congr 1
  funext a
  fin_cases a <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04CompAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04CompAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04CompAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.rm04CompAt_apply

omit [FiniteDimensional ℝ E] in
theorem tensor0SSpace_sum_apply {ι : Type*} [Fintype ι] {s : ℕ}
    (T : ι -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  exact Tensor0SSpace.sum_apply (I := I) Finset.univ s x T v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SSpace_sum_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SSpace_sum_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SSpace_sum_apply ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SSpace_sum_apply

omit [DecidableEq Idx] in
private theorem basisTensor0S_empty_eq_scalarOne
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (slots : Fin 0 -> Idx) :
    basisTensor0S (I := I) basis slots = scalarOne0S (I := I) x := by
  classical
  ext v
  have hv : v = Fin.elim0 := Subsingleton.elim _ _
  rw [hv]
  have hcomp := basisTensor0S_component (I := I) basis slots slots
  have harg : (fun a : Fin 0 => basis (slots a)) = Fin.elim0 := Subsingleton.elim _ _
  change (basisTensor0S (I := I) basis slots) (fun a : Fin 0 => basis (slots a)) = 1
    at hcomp
  rw [harg] at hcomp
  rw [show (scalarOne0S (I := I) x) Fin.elim0 = 1 by
    exact ContinuousMultilinearMap.constOfIsEmpty_apply Real
      (fun _ : Fin 0 => TangentSpace I x) 1 Fin.elim0]
  exact hcomp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.basisTensor0S_empty_eq_scalarOne
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.basisTensor0S_empty_eq_scalarOne target :: scope.openDecls } }

omit [DecidableEq Idx] in
theorem ricciCompAt_eq_contractTrace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ricciCompAt (I := I) basis (ricciFromRm13At (I := I) (M := M) Rm13) i j =
      componentRSField (I := I) basis
        (contractTrace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        Fin.elim0 (slots2 i j) := by
  unfold ricciCompAt componentRSField ricciFromRm13At
    component0S
  rw [basisTensor0S_empty_eq_scalarOne (I := I) basis Fin.elim0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_contractTrace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_contractTrace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_contractTrace ``Submission.DifferentialGeometry.Geometry.Curvature.ricciCompAt_eq_contractTrace

omit [DecidableEq Idx] in
theorem contract_trace13_component_basis
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x) (i j : Idx) :
    ((contractTrace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
        (scalarOne0S (I := I) x)) (vec2 (basis i) (basis j)) =
      ∑ a : Idx,
        Rm13 (dualToCotangent (I := I) (basis.coord a))
          (vec3 (basis a) (basis i) (basis j)) := by
  have : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by simp)
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
  let := tensorRSBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2
  let := tensorRSBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3
  let tangentModel := tangentSpaceModelContinuousLinearEquiv (I := I) x
  let basisModel : Module.Basis Idx Real E := basis.map tangentModel.toLinearEquiv
  unfold contractTrace
  change ((modelContractTrace (𝕜 := Real) (E := E) 0 2
      (TensorRSSpace.toModel (I := I) Rm13))
      (Tensor0SSpace.toModel (I := I) (scalarOne0S (I := I) x)))
      (fun k => tangentModel (vec2 (basis i) (basis j) k)) = _
  rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basisModel 0 2]
  refine Finset.sum_congr rfl fun a _ => ?_
  let covM : Tensor0SModel 1 Real E :=
    (continuousMultilinearCurryFin1 Real E Real).symm
      (LinearMap.toContinuousLinearMap (basisModel.coord a))
  have hinput :
      Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1) =
        covM := by
    ext v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    change (basisModel.coord a) (v 0) * 1 = (basisModel.coord a) (v 0)
    ring
  simp only [modelInteriorProduct, modelTensorWithCovectorFirst, modelCovectorOfCLM,
    scalarOne0S, TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpaceContinuousLinearEquiv]
  change (Rm13
      (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
        (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1)))
      (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) (basis i) (basis j))
  have hleft :
      (Rm13
        (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1)))
        (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
      (Rm13 covM) (Fin.cons (basis a) (vec2 (basis i) (basis j))) := by
    exact congrArg
      (fun U => (Rm13 U) (Fin.cons (basis a) (vec2 (basis i) (basis j)))) hinput
  rw [hleft]
  change (Rm13 (dualToCotangent (I := I) (basis.coord a)))
      (Fin.cons (basis a) (vec2 (basis i) (basis j))) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) (basis i) (basis j))
  congr 1
  funext q
  fin_cases q
  · rfl
  · rfl
  · change vec2 (basis i) (basis j) 1 = basis j
    simp [vec2, DifferentialGeometry.Geometry.Curvature.vec2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.contract_trace13_component_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.contract_trace13_component_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.contract_trace13_component_basis ``Submission.DifferentialGeometry.Geometry.Curvature.contract_trace13_component_basis

omit [DecidableEq Idx] in
theorem ricciFromRm13At_apply_basis_trace
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (Rm13 : Tensor13At (I := I) (M := M) x)
    (Y Z : TangentSpace I x) :
    ricciFromRm13At (I := I) (M := M) Rm13 (vec2 Y Z) =
      ∑ a : Idx,
        Rm13 (dualToCotangent (I := I) (basis.coord a))
          (vec3 (basis a) Y Z) := by
  have : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M) (n := ∞) (by simp)
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
  let := tensor0SBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
  let := tensorRSBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2
  let := tensorRSBundleTopology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3
  let tangentModel := tangentSpaceModelContinuousLinearEquiv (I := I) x
  let basisModel : Module.Basis Idx Real E := basis.map tangentModel.toLinearEquiv
  change ((contractTrace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
      (scalarOne0S (I := I) x)) (vec2 Y Z) = _
  unfold contractTrace
  change ((modelContractTrace (𝕜 := Real) (E := E) 0 2
      (TensorRSSpace.toModel (I := I) Rm13))
      (Tensor0SSpace.toModel (I := I) (scalarOne0S (I := I) x)))
      (fun k => tangentModel (vec2 Y Z k)) = _
  rw [model_contract_trace_apply_basis (𝕜 := Real) (E := E) basisModel 0 2]
  refine Finset.sum_congr rfl fun a _ => ?_
  let covM : Tensor0SModel 1 Real E :=
    (continuousMultilinearCurryFin1 Real E Real).symm
      (LinearMap.toContinuousLinearMap (basisModel.coord a))
  have hinput :
      Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1) =
        covM := by
    ext v
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    change (basisModel.coord a) (v 0) * 1 = (basisModel.coord a) (v 0)
    ring
  simp only [modelInteriorProduct, modelTensorWithCovectorFirst, modelCovectorOfCLM,
    scalarOne0S, TensorRSSpace.toModel, Tensor0SSpace.toModel,
    tensorRSSpaceContinuousLinearEquiv]
  change (Rm13
      (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
        (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1)))
      (Fin.cons (basis a) (vec2 Y Z)) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) Y Z)
  have hleft :
      (Rm13
        (Bundle.continuousMultilinearMap.modelProduct 1 0 covM
          (ContinuousMultilinearMap.constOfIsEmpty Real (fun _ : Fin 0 => E) 1)))
        (Fin.cons (basis a) (vec2 Y Z)) =
      (Rm13 covM) (Fin.cons (basis a) (vec2 Y Z)) := by
    exact congrArg
      (fun U => (Rm13 U) (Fin.cons (basis a) (vec2 Y Z))) hinput
  rw [hleft]
  change (Rm13 (dualToCotangent (I := I) (basis.coord a)))
      (Fin.cons (basis a) (vec2 Y Z)) =
    Rm13 (dualToCotangent (I := I) (basis.coord a)) (vec3 (basis a) Y Z)
  congr 1
  funext q
  fin_cases q
  · rfl
  · rfl
  · change vec2 Y Z 1 = Z
    simp [vec2, DifferentialGeometry.Geometry.Curvature.vec2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciFromRm13At_apply_basis_trace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciFromRm13At_apply_basis_trace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciFromRm13At_apply_basis_trace ``Submission.DifferentialGeometry.Geometry.Curvature.ricciFromRm13At_apply_basis_trace
end DifferentialGeometry.Geometry.Curvature
