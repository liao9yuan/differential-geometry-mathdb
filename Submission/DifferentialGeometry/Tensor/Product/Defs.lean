/-
Authors: Yuan Liao, Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Product.HomEquiv
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs

import Submission.DifferentialGeometry.Tensor.Alternating.Curry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Topology _root_.TensorProduct

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

section MapL

variable {G₁ G₂ : Type*}
  [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [FiniteDimensional 𝕜 G₁]
  [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [FiniteDimensional 𝕜 G₂]

open _root_.TensorProduct in
noncomputable def TensorProduct.mapLFiniteDimensional (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    (F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂) :=
  (TensorProduct.map L₁.toLinearMap L₂.toLinearMap).toContinuousLinearMap

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.TensorProduct
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLFiniteDimensional then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLFiniteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLFiniteDimensional ``Submission.TensorProduct.mapLFiniteDimensional

omit [FiniteDimensional 𝕜 G₂] in
open _root_.TensorProduct in
@[simp]
theorem TensorProduct.mapLFiniteDimensional_tmul (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) (v : F₁) (w : F₂) :
    TensorProduct.mapLFiniteDimensional L₁ L₂ (v ⊗ₜ w) = L₁ v ⊗ₜ L₂ w := by
  simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_tmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLFiniteDimensional_tmul then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLFiniteDimensional_tmul"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLFiniteDimensional_tmul ``Submission.TensorProduct.mapLFiniteDimensional_tmul

omit [FiniteDimensional 𝕜 G₂] in
open _root_.TensorProduct in
theorem TensorProduct.mapLFiniteDimensional_add_left (L₁ L₁' : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional (L₁ + L₁') L₂ =
      TensorProduct.mapLFiniteDimensional L₁ L₂ + TensorProduct.mapLFiniteDimensional L₁' L₂ := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_add_left]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLFiniteDimensional_add_left then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLFiniteDimensional_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLFiniteDimensional_add_left ``Submission.TensorProduct.mapLFiniteDimensional_add_left

omit [FiniteDimensional 𝕜 G₂] in
open _root_.TensorProduct in
theorem TensorProduct.mapLFiniteDimensional_add_right (L₁ : F₁ →L[𝕜] G₁) (L₂ L₂' : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional L₁ (L₂ + L₂') =
      TensorProduct.mapLFiniteDimensional L₁ L₂ + TensorProduct.mapLFiniteDimensional L₁ L₂' := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_add_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLFiniteDimensional_add_right then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLFiniteDimensional_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLFiniteDimensional_add_right ``Submission.TensorProduct.mapLFiniteDimensional_add_right

omit [FiniteDimensional 𝕜 G₂] in
open _root_.TensorProduct in
theorem TensorProduct.mapLFiniteDimensional_smul_left (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional (c • L₁) L₂ = c • TensorProduct.mapLFiniteDimensional L₁ L₂ := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_smul_left]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLFiniteDimensional_smul_left then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLFiniteDimensional_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLFiniteDimensional_smul_left ``Submission.TensorProduct.mapLFiniteDimensional_smul_left

omit [FiniteDimensional 𝕜 G₂] in
open _root_.TensorProduct in
theorem TensorProduct.mapLFiniteDimensional_smul_right (c : 𝕜) (L₁ : F₁ →L[𝕜] G₁) (L₂ : F₂ →L[𝕜] G₂) :
    TensorProduct.mapLFiniteDimensional L₁ (c • L₂) = c • TensorProduct.mapLFiniteDimensional L₁ L₂ := by
  ext x; simp [TensorProduct.mapLFiniteDimensional, TensorProduct.map_smul_right]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLFiniteDimensional_smul_right then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLFiniteDimensional_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLFiniteDimensional_smul_right ``Submission.TensorProduct.mapLFiniteDimensional_smul_right

open _root_.TensorProduct in
noncomputable def TensorProduct.mapLBilinear :
    (F₁ →L[𝕜] G₁) →L[𝕜] (F₂ →L[𝕜] G₂) →L[𝕜]
      ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) := by
  classical
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] G₁) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 (F₂ →L[𝕜] G₂) := ContinuousLinearMap.finiteDimensional
  haveI : FiniteDimensional 𝕜 ((F₂ →L[𝕜] G₂) →L[𝕜] F₁ ⊗[𝕜] F₂ →L[𝕜] G₁ ⊗[𝕜] G₂)
    := ContinuousLinearMap.finiteDimensional
  let innerLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →ₗ[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    { toFun := fun L₂ => TensorProduct.mapLFiniteDimensional (𝕜 := 𝕜) L₁ L₂
      map_add' := TensorProduct.mapLFiniteDimensional_add_right (𝕜 := 𝕜) (L₁ := L₁)
      map_smul' := fun c L₂ =>
        TensorProduct.mapLFiniteDimensional_smul_right (𝕜 := 𝕜) (L₁ := L₁) (L₂ := L₂) c }
  let innerCLM (L₁ : F₁ →L[𝕜] G₁) :
      (F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)) :=
    (innerLM (L₁ := L₁)).toContinuousLinearMap
  let outerLM :
      (F₁ →L[𝕜] G₁) →ₗ[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    { toFun := fun L₁ => innerCLM (L₁ := L₁)
      map_add' := by
        intro L₁ L₁'
        ext L₂ x
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapLFiniteDimensional_add_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) (L₁' := L₁'))
      map_smul' := by
        intro c L₁
        ext L₂ x
        simpa [innerCLM, innerLM] using congrArg (fun f => f x)
          (TensorProduct.mapLFiniteDimensional_smul_left (𝕜 := 𝕜) (L₂ := L₂) (L₁ := L₁) c) }
  have h : Continuous outerLM := @LinearMap.continuous_of_finiteDimensional
    _ _ (F₁ →L[𝕜] G₁) _ _ _ _ _ ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂)))
    _ _ _ _ _ _ _ _ outerLM
  let f : (F₁ →L[𝕜] G₁) →L[𝕜]
        ((F₂ →L[𝕜] G₂) →L[𝕜] ((F₁ ⊗[𝕜] F₂) →L[𝕜] (G₁ ⊗[𝕜] G₂))) :=
    ContinuousLinearMap.mk outerLM h
  exact f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLBilinear then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLBilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLBilinear ``Submission.TensorProduct.mapLBilinear

open _root_.TensorProduct in
theorem TensorProduct.mapLBilinear_contDiff :
    ContDiff 𝕜 ⊤ (fun p : (F₁ →L[𝕜] G₁) × (F₂ →L[𝕜] G₂) =>
      TensorProduct.mapLBilinear (𝕜 := 𝕜) p.1 p.2) :=
  ((TensorProduct.mapLBilinear (𝕜 := 𝕜) (F₁ := F₁) (G₁ := G₁)
    (F₂ := F₂) (G₂ := G₂)).contDiff.comp contDiff_fst).clm_apply
    (contDiff_snd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `TensorProduct.mapLBilinear_contDiff then
    throwError "Refusing to shadow existing declaration TensorProduct.mapLBilinear_contDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `TensorProduct.mapLBilinear_contDiff ``Submission.TensorProduct.mapLBilinear_contDiff

end MapL

namespace DifferentialGeometry
namespace Tensor0SBundle

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap

open scoped _root_.Manifold _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]

end Tensor0SBundle
end DifferentialGeometry

namespace ContinuousAlternatingMap
open _root_.ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

open _root_.ContinuousAlternatingMap in
def tensorProductMap (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (m + n) => M) N'' :=
  (ContinuousMultilinearMap.uncurrySum
    ((f.compContinuousAlternatingMap₂ g h).toContinuousMultilinearMap
      |>.flipAlternating.toContinuousMultilinearMap.flipMultilinear))
  |>.domDomCongr finSumFinEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.tensorProductMap then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.tensorProductMap"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.tensorProductMap ``Submission.ContinuousAlternatingMap.tensorProductMap

open _root_.ContinuousAlternatingMap in
@[simp]
theorem tensorProductMap_apply (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (w : Fin (m + n) → M) :
    tensorProductMap g h f w =
      f (g (w ∘ Fin.castAdd n)) (h (w ∘ Fin.natAdd m)) := by
  unfold tensorProductMap
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.flipMultilinear_apply,
    _root_.ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
    ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContinuousAlternatingMap.tensorProductMap_apply then
    throwError "Refusing to shadow existing declaration ContinuousAlternatingMap.tensorProductMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `ContinuousAlternatingMap.tensorProductMap_apply ``Submission.ContinuousAlternatingMap.tensorProductMap_apply

end ContinuousAlternatingMap
