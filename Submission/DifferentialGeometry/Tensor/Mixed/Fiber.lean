/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

namespace Bundle.continuousMultilinearMap
open _root_.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {r s : ℕ}

private theorem mixed_type_eq (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => E x) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) := by
  unfold Bundle.continuousMultilinearMap
  congr 1 <;> exact topology_eq (𝕜 := 𝕜) (F := F) (E := E) _ x

run_cmd do
  let target := ``Submission.Bundle.continuousMultilinearMap.mixed_type_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.continuousMultilinearMap.mixed_type_eq target :: scope.openDecls } }

private def mixed_normedInstances (r s : ℕ) (x : B) :
    Σ' (ng : NormedAddCommGroup
          (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
           Bundle.continuousMultilinearMap 𝕜 s F E x)),
      @NormedSpace 𝕜
        (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x)
        _ ng.toSeminormedAddCommGroup :=
  (mixed_type_eq (𝕜 := 𝕜) (F := F) (E := E) r s x) ▸ ⟨inferInstance, inferInstance⟩

run_cmd do
  let target := ``Submission.Bundle.continuousMultilinearMap.mixed_normedInstances
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.continuousMultilinearMap.mixed_normedInstances target :: scope.openDecls } }

instance mixedInstNormedAddCommGroup (r s : ℕ) (x : B) :
    NormedAddCommGroup
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  (mixed_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r s x).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup ``Submission.Bundle.continuousMultilinearMap.mixedInstNormedAddCommGroup

instance mixedInstNormedSpace (r s : ℕ) (x : B) :
    NormedSpace 𝕜
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  (mixed_normedInstances (𝕜 := 𝕜) (F := F) (E := E) r s x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedInstNormedSpace then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedInstNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedInstNormedSpace ``Submission.Bundle.continuousMultilinearMap.mixedInstNormedSpace

instance mixed_instContinuousSMul (r s : ℕ) (x : B) :
    ContinuousSMul 𝕜
      (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
       Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixed_instContinuousSMul then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixed_instContinuousSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixed_instContinuousSMul ``Submission.Bundle.continuousMultilinearMap.mixed_instContinuousSMul

def mixedContinuousLinearEquivAt (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x) ≃L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r x).arrowCongr
    (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt ``Submission.Bundle.continuousMultilinearMap.mixedContinuousLinearEquivAt

def mixedToModel {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel ``Submission.Bundle.continuousMultilinearMap.mixedToModel

def mixedToModelL (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
     Bundle.continuousMultilinearMap 𝕜 s F E x) →L[𝕜]
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
     ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModelL then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModelL"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModelL ``Submission.Bundle.continuousMultilinearMap.mixedToModelL

def mixedOfModel {r s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).symm.toContinuousLinearMap f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedOfModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedOfModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedOfModel ``Submission.Bundle.continuousMultilinearMap.mixedOfModel

@[simp]
theorem mixedToModelL_apply {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (mixedToModelL (𝕜 := 𝕜) (F := F) (E := E) r s x).toFun T = mixedToModel T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModelL_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModelL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModelL_apply ``Submission.Bundle.continuousMultilinearMap.mixedToModelL_apply

@[simp]
theorem mixedToModel_add {r s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
             Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (T₁ + T₂) =
      mixedToModel T₁ + mixedToModel T₂ :=
  map_add (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap
    T₁ T₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_add then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_add"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_add ``Submission.Bundle.continuousMultilinearMap.mixedToModel_add

@[simp]
theorem mixedToModel_smul {r s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                  Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (c • T) = c • mixedToModel T :=
  map_smul (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap
    c T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_smul then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_smul ``Submission.Bundle.continuousMultilinearMap.mixedToModel_smul

@[simp]
theorem mixedToModel_zero {r s : ℕ} {x : B} :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
           Bundle.continuousMultilinearMap 𝕜 s F E x) = 0 :=
  map_zero (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_zero then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_zero ``Submission.Bundle.continuousMultilinearMap.mixedToModel_zero

@[simp]
theorem mixedToModel_neg {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (-T) = -mixedToModel T := by
  ext m; simp only [mixedToModel, neg_apply]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_neg then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_neg ``Submission.Bundle.continuousMultilinearMap.mixedToModel_neg

@[simp]
theorem mixedToModel_sub {r s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
             Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (T₁ - T₂) =
      mixedToModel T₁ - mixedToModel T₂ := by
  ext m; simp only [mixedToModel, sub_apply]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_sub then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_sub ``Submission.Bundle.continuousMultilinearMap.mixedToModel_sub

@[simp]
theorem mixedOfModel_mixedToModel {r s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
         Bundle.continuousMultilinearMap 𝕜 s F E x) :
    mixedOfModel (𝕜 := 𝕜) (F := F) (E := E) (mixedToModel T) = T :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).left_inv T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedOfModel_mixedToModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedOfModel_mixedToModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedOfModel_mixedToModel ``Submission.Bundle.continuousMultilinearMap.mixedOfModel_mixedToModel

@[simp]
theorem mixedToModel_mixedOfModel {r s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
         ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    mixedToModel (𝕜 := 𝕜) (F := F) (E := E) (mixedOfModel (x := x) f) = f :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).right_inv f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_mixedOfModel then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_mixedOfModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_mixedOfModel ``Submission.Bundle.continuousMultilinearMap.mixedToModel_mixedOfModel

theorem mixedToModel_continuous {r s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).toContinuousLinearMap.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_continuous then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_continuous ``Submission.Bundle.continuousMultilinearMap.mixedToModel_continuous

theorem mixedToModel_injective {r s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_injective then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_injective ``Submission.Bundle.continuousMultilinearMap.mixedToModel_injective

theorem mixedToModel_surjective {r s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).surjective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_surjective then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_surjective ``Submission.Bundle.continuousMultilinearMap.mixedToModel_surjective

theorem mixedToModel_bijective {r s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
              Bundle.continuousMultilinearMap 𝕜 s F E x =>
        mixedToModel (𝕜 := 𝕜) (F := F) (E := E) T) :=
  (mixedContinuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) r s x).bijective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedToModel_bijective then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedToModel_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedToModel_bijective ``Submission.Bundle.continuousMultilinearMap.mixedToModel_bijective

end Bundle.continuousMultilinearMap

end
