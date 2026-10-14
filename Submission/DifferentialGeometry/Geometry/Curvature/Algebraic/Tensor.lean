import Submission.DifferentialGeometry.Geometry.Curvature.Algebraic.Form
import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.Tensor
import Submission.DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

omit [FiniteDimensional Real E] in
private theorem tensor04StandardAt_add_left {x : M}
    (A : Tensor04At (I := I) (M := M) x)
    (x₁ x₂ y z w : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M) A (x₁ + x₂) y z w =
      tensor04StandardAt (I := I) (M := M) A x₁ y z w +
        tensor04StandardAt (I := I) (M := M) A x₂ y z w := by
  have h := A.map_update_add (vec4 (I := I) 0 y z w) (0 : Fin 4) x₁ x₂
  have hupdate (v : TangentSpace I x) :
      Function.update (vec4 (I := I) 0 y z w) (0 : Fin 4) v =
        vec4 (I := I) v y z w := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hupdate (x₁ + x₂), hupdate x₁, hupdate x₂] at h
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_add_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_add_left target :: scope.openDecls } }

omit [FiniteDimensional Real E] in
private theorem tensor04StandardAt_smul_left {x : M}
    (A : Tensor04At (I := I) (M := M) x)
    (a : Real) (v y z w : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M) A (a • v) y z w =
      a * tensor04StandardAt (I := I) (M := M) A v y z w := by
  have h := A.map_update_smul (vec4 (I := I) 0 y z w) (0 : Fin 4) a v
  have hupdate (u : TangentSpace I x) :
      Function.update (vec4 (I := I) 0 y z w) (0 : Fin 4) u =
        vec4 (I := I) u y z w := by
    funext i
    fin_cases i <;> simp [vec4]
  rw [hupdate (a • v), hupdate v] at h
  change A (vec4 (I := I) (a • v) y z w) =
    a * A (vec4 (I := I) v y z w)
  exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_smul_left
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_smul_left target :: scope.openDecls } }

noncomputable def algebraicCurvatureTensorSubmodule (x : M) :
    Submodule Real (Tensor04At (I := I) (M := M) x) where
  carrier := {A | IsAlgCurvForm (tensor04StandardAt (I := I) (M := M) A)}
  zero_mem' := by
    change IsAlgCurvForm (fun _ _ _ _ : TangentSpace I x => 0)
    exact IsAlgCurvForm.zero
  add_mem' := by
    intro A B hA hB
    change IsAlgCurvForm (fun x y z w =>
      tensor04StandardAt A x y z w + tensor04StandardAt B x y z w)
    exact hA.add hB
  smul_mem' := by
    intro c A hA
    change IsAlgCurvForm (fun x y z w => c * tensor04StandardAt A x y z w)
    exact hA.smul c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule

omit [FiniteDimensional Real E] in
@[simp]
theorem mem_algebraicCurvatureTensorSubmodule {x : M}
    {A : Tensor04At (I := I) (M := M) x} :
    A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      IsAlgCurvForm (tensor04StandardAt (I := I) (M := M) A) :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule ``Submission.DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule

omit [FiniteDimensional Real E] in
theorem mem_algebraicCurvatureTensorSubmodule_iff_symmetries {x : M}
    {A : Tensor04At (I := I) (M := M) x} :
    A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      (∀ X Y Z W : TangentSpace I x,
        tensor04StandardAt (I := I) (M := M) A X Y Z W =
          -tensor04StandardAt (I := I) (M := M) A Y X Z W) ∧
      (∀ X Y Z W : TangentSpace I x,
        tensor04StandardAt (I := I) (M := M) A X Y Z W =
          -tensor04StandardAt (I := I) (M := M) A X Y W Z) ∧
      (∀ X Y Z W : TangentSpace I x,
        tensor04StandardAt (I := I) (M := M) A X Y Z W +
          tensor04StandardAt (I := I) (M := M) A Y Z X W +
          tensor04StandardAt (I := I) (M := M) A Z X Y W = 0) := by
  constructor
  · intro hA
    have hForm := mem_algebraicCurvatureTensorSubmodule.mp hA
    exact ⟨hForm.anti_first, hForm.anti_last, hForm.bianchi⟩
  · rintro ⟨hFirst, hLast, hBianchi⟩
    apply mem_algebraicCurvatureTensorSubmodule.mpr
    exact
      { add_left := tensor04StandardAt_add_left (I := I) (M := M) A
        smul_left := tensor04StandardAt_smul_left (I := I) (M := M) A
        anti_first := hFirst
        anti_last := hLast
        bianchi := hBianchi }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule_iff_symmetries then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule_iff_symmetries"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule_iff_symmetries ``Submission.DifferentialGeometry.Geometry.Curvature.mem_algebraicCurvatureTensorSubmodule_iff_symmetries

omit [FiniteDimensional Real E] in
theorem tensor04StandardAt_compContinuousLinearMap
    {x : M} (A : Tensor04At (I := I) (M := M) x)
    (L : TangentSpace I x →L[Real] TangentSpace I x)
    (X Y Z W : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M)
        (A.compContinuousLinearMap (fun _ : Fin 4 => L)) X Y Z W =
      tensor04StandardAt (I := I) (M := M) A (L X) (L Y) (L Z) (L W) := by
  change (A : ContinuousMultilinearMap Real (fun _ : Fin 4 => TangentSpace I x) Real)
      (fun i : Fin 4 => L (vec4 X Y Z W i)) =
    (A : ContinuousMultilinearMap Real (fun _ : Fin 4 => TangentSpace I x) Real)
      (vec4 (L X) (L Y) (L Z) (L W))
  congr 1
  funext i
  fin_cases i <;> simp [vec4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_compContinuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_compContinuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_compContinuousLinearMap ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_compContinuousLinearMap

omit [FiniteDimensional Real E] in
theorem compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule
    {x : M} (L : TangentSpace I x →L[Real] TangentSpace I x)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (A : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => L) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  have hA : IsAlgCurvForm
      (tensor04StandardAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)) :=
    mem_algebraicCurvatureTensorSubmodule.mp A.2
  change IsAlgCurvForm (fun X Y Z W =>
    tensor04StandardAt (I := I) (M := M)
      ((A : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => L)) X Y Z W)
  simp_rw [tensor04StandardAt_compContinuousLinearMap]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y Z W
    rw [map_add]
    exact hA.add_left _ _ _ _ _
  · intro a X Y Z W
    rw [map_smul]
    exact hA.smul_left _ _ _ _ _
  · exact fun X Y Z W => hA.anti_first _ _ _ _
  · exact fun X Y Z W => hA.anti_last _ _ _ _
  · exact fun X Y Z W => hA.bianchi _ _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule ``Submission.DifferentialGeometry.Geometry.Curvature.compContinuousLinearMap_mem_algebraicCurvatureTensorSubmodule

omit [FiniteDimensional Real E] in
theorem tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule
    {x : M} {A : Tensor04At (I := I) (M := M) x}
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M) A X Y Z W =
      tensor04StandardAt (I := I) (M := M) A Z W X Y :=
  (mem_algebraicCurvatureTensorSubmodule.mp hA).pair_swap X Y Z W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pair_swap_of_mem_algebraicCurvatureTensorSubmodule

theorem tensor04StandardAt_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor04At (I := I) (M := M) y)
    (v₀ v₁ v₂ v₃ : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) v₀ v₁ v₂ v₃ =
      tensor04StandardAt (I := I) (M := M) A (e v₀) (e v₁) (e v₂) (e v₃) := by
  unfold tensor04StandardAt
  rw [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply]
  congr 1
  funext i
  fin_cases i <;> simp [vec4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pullback ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_pullback

theorem tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff
    {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor04At (I := I) (M := M) y) :
    tensor0SPullbackCLE (I := I) (M := M) 4 e A ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) y := by
  constructor
  · intro hA
    have hPull := mem_algebraicCurvatureTensorSubmodule.mp hA
    apply mem_algebraicCurvatureTensorSubmodule.mpr
    refine
      { add_left := ?_
        smul_left := ?_
        anti_first := ?_
        anti_last := ?_
        bianchi := ?_ }
    · intro x₁ x₂ z w q
      exact tensor04StandardAt_add_left (I := I) (M := M) A x₁ x₂ z w q
    · intro a x z w q
      exact tensor04StandardAt_smul_left (I := I) (M := M) A a x z w q
    · intro v₀ v₁ v₂ v₃
      have h := hPull.anti_first
        (e.symm v₀) (e.symm v₁) (e.symm v₂) (e.symm v₃)
      rw [tensor04StandardAt_pullback, tensor04StandardAt_pullback] at h
      simpa using h
    · intro v₀ v₁ v₂ v₃
      have h := hPull.anti_last
        (e.symm v₀) (e.symm v₁) (e.symm v₂) (e.symm v₃)
      rw [tensor04StandardAt_pullback, tensor04StandardAt_pullback] at h
      simpa using h
    · intro v₀ v₁ v₂ v₃
      have h := hPull.bianchi
        (e.symm v₀) (e.symm v₁) (e.symm v₂) (e.symm v₃)
      rw [tensor04StandardAt_pullback, tensor04StandardAt_pullback,
        tensor04StandardAt_pullback] at h
      simpa using h
  · intro hA
    have hForm := mem_algebraicCurvatureTensorSubmodule.mp hA
    apply mem_algebraicCurvatureTensorSubmodule.mpr
    refine
      { add_left := ?_
        smul_left := ?_
        anti_first := ?_
        anti_last := ?_
        bianchi := ?_ }
    · intro x₁ x₂ z w q
      exact tensor04StandardAt_add_left (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) x₁ x₂ z w q
    · intro a x z w q
      exact tensor04StandardAt_smul_left (I := I) (M := M)
        (tensor0SPullbackCLE (I := I) (M := M) 4 e A) a x z w q
    · intro v₀ v₁ v₂ v₃
      rw [tensor04StandardAt_pullback, tensor04StandardAt_pullback]
      exact hForm.anti_first (e v₀) (e v₁) (e v₂) (e v₃)
    · intro v₀ v₁ v₂ v₃
      rw [tensor04StandardAt_pullback, tensor04StandardAt_pullback]
      exact hForm.anti_last (e v₀) (e v₁) (e v₂) (e v₃)
    · intro v₀ v₁ v₂ v₃
      rw [tensor04StandardAt_pullback, tensor04StandardAt_pullback,
        tensor04StandardAt_pullback]
      exact hForm.bianchi (e v₀) (e v₁) (e v₂) (e v₃)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff ``Submission.DifferentialGeometry.Geometry.Curvature.tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff

theorem algebraicCurvatureTensorSubmodule_map_pullback {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) y).map
        (tensor0SPullbackCLE (I := I) (M := M) 4 e).toLinearMap =
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  apply Submodule.ext
  intro A
  rw [Submodule.mem_map_equiv]
  simpa using tensor0SPullbackCLE_mem_algebraicCurvatureTensorSubmodule_iff
    (I := I) (M := M) e.symm A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule_map_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule_map_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule_map_pullback ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorSubmodule_map_pullback

noncomputable def algebraicCurvatureTensorPullbackCLE {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    algebraicCurvatureTensorSubmodule (I := I) (M := M) y ≃L[Real]
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
  (tensor0SPullbackCLE (I := I) (M := M) 4 e).ofSubmodules
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) y)
    (algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (algebraicCurvatureTensorSubmodule_map_pullback (I := I) (M := M) e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE

@[simp]
theorem algebraicCurvatureTensorPullbackCLE_apply {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) y) :
    (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e A :
      Tensor04At (I := I) (M := M) x) =
        tensor0SPullbackCLE (I := I) (M := M) 4 e A :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_apply ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_apply

@[simp]
theorem algebraicCurvatureTensorPullbackCLE_symm {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y) :
    (algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e).symm =
      algebraicCurvatureTensorPullbackCLE (I := I) (M := M) e.symm := by
  apply ContinuousLinearEquiv.ext
  funext A
  apply Subtype.ext
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_symm ``Submission.DifferentialGeometry.Geometry.Curvature.algebraicCurvatureTensorPullbackCLE_symm

end DifferentialGeometry.Geometry.Curvature
