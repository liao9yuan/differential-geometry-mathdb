import Submission.DifferentialGeometry.Tensor.RSTensor.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞} [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def TensorRSField.rs0 {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  tensorRSFieldApplyInput (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) n T
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) n)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0 ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.rs0_apply {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    TensorRSField.rs0 (n := n) T x =
      T x (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) := by
  rw [TensorRSField.rs0, tensorRSField_applyInput_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_apply ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_apply

omit [IsManifold I (n + 1) M] in
private theorem rankZero_eq_smul_one
    (x : M) (c : Tensor0SSpace 0 I x) :
    c = tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c •
      Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x := by
  apply (tensor0SSpaceContinuousLinearEquiv 0 x).injective
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.toModel c v =
    Tensor0SSpace.toModel
      (tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c •
        Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) n x) v
  rw [Tensor0SSpace.toModel_smul, smul_apply, smul_eq_mul,
    Tensor0SSpace.evalScalar_apply]
  have hone : Tensor0SSpace.toModel
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) v = (1 : 𝕜) :=
    Tensor0SField.one0_apply (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n x v
  rw [hone, mul_one]
  exact congrArg (Tensor0SSpace.toModel c) (Subsingleton.elim v Fin.elim0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.rankZero_eq_smul_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.rankZero_eq_smul_one target :: scope.openDecls } }

omit [IsManifold I (n + 1) M] in
theorem TensorRSField.toRS0_rs0 {s : ℕ}
    (T : TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (TensorRSField.rs0 (n := n) T).toTensorRSField n = T := by
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro c
  rw [Tensor0SField.toRS0_apply, TensorRSField.rs0_apply]
  calc
    tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c •
          T x (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) n x) =
        T x (tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c •
          Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) n x) := by
          rw [map_smul]
    _ = T x c := congrArg (T x) (rankZero_eq_smul_one (n := n) x c).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.toRS0_rs0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.toRS0_rs0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.toRS0_rs0 ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.toRS0_rs0

omit [IsManifold I (n + 1) M] in
theorem TensorRSField.rs0_toRS0 {s : ℕ}
    (A : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.rs0 (n := n) (A.toTensorRSField n) = A := by
  apply ContMDiffSection.ext
  intro x
  rw [TensorRSField.rs0_apply, Tensor0SField.toRS0_apply]
  have hone : tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x
      (Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) n x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    exact Tensor0SField.one0_apply (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n x Fin.elim0
  rw [hone, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_toRS0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_toRS0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_toRS0 ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.rs0_toRS0

noncomputable def TensorRSField.scalar0
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    M → 𝕜 :=
  (TensorRSField.rs0 (n := n) T).toScalarField n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0 ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0

theorem TensorRSField.scalar0_smooth
  (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) n (TensorRSField.scalar0 (n := n) T) :=
  Tensor0SField.toScalarField_contMDiff n inferInstance (TensorRSField.rs0 (n := n) T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smooth ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smooth

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_zero :
    TensorRSField.scalar0 (n := n)
        (0 : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) =
      0 := by
  funext x
  simp only [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, ContMDiffSection.coe_zero, Pi.zero_apply]
  rw [TensorRSSpace.zero_apply, Tensor0SSpace.toModel_zero, _root_.zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_zero ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_zero

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_add
    (S T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (S + T) =
      TensorRSField.scalar0 (n := n) S + TensorRSField.scalar0 (n := n) T := by
  funext x
  simp only [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, ContMDiffSection.coe_add, Pi.add_apply]
  rw [TensorRSSpace.add_apply, Tensor0SSpace.toModel_add, _root_.add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_add ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_add

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_smul
    (c : 𝕜)
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (c • T) =
      c • TensorRSField.scalar0 (n := n) T := by
  funext x
  simp only [TensorRSField.scalar0, Tensor0SField.toScalarField,
    TensorRSField.rs0_apply, ContMDiffSection.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [TensorRSSpace.smul_apply, Tensor0SSpace.toModel_smul,
    _root_.smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smul ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_smul

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_neg
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (-T) =
      -TensorRSField.scalar0 (n := n) T := by
  rw [show -T = (-1 : 𝕜) • T by simp, TensorRSField.scalar0_smul]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_neg ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_neg

omit [IsManifold I (n + 1) M] in
@[simp]
theorem TensorRSField.scalar0_sub
    (S T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField.scalar0 (n := n) (S - T) =
      TensorRSField.scalar0 (n := n) S - TensorRSField.scalar0 (n := n) T := by
  rw [sub_eq_add_neg, TensorRSField.scalar0_add, TensorRSField.scalar0_neg]
  rw [sub_eq_add_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_sub ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.scalar0_sub

theorem TensorRSField.lift_scalar0
    (T : TensorRSField n 0 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (Tensor0SField.fromScalarField n (TensorRSField.scalar0 (n := n) T)
      (TensorRSField.scalar0_smooth (n := n) T)).toTensorRSField n = T := by
  calc
    (Tensor0SField.fromScalarField n (TensorRSField.scalar0 (n := n) T)
          (TensorRSField.scalar0_smooth (n := n) T)).toTensorRSField n =
        (TensorRSField.rs0 (n := n) T).toTensorRSField n := by
          congr 1
          simp [TensorRSField.scalar0]
    _ = T := TensorRSField.toRS0_rs0 (n := n) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TensorRSField.lift_scalar0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TensorRSField.lift_scalar0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TensorRSField.lift_scalar0 ``Submission.DifferentialGeometry.Tensor0SBundle.TensorRSField.lift_scalar0

end

end Tensor0SBundle
end DifferentialGeometry
