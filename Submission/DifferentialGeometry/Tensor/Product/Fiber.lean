/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.Topology.VectorBundle.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Product

noncomputable section

open _root_.Bundle _root_.Set

open scoped _root_.TensorProduct _root_.Topology

section TensorProductFiber

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace Bundle.TensorProduct
open _root_.Bundle

@[reducible] noncomputable def tensorFiberTopology (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
  TopologicalSpace.induced
    (TensorProduct.map
      ((_root_.FiberBundle.trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
        (_root_.FiberBundle.mem_baseSet_trivializationAt F₁ E₁ x)).toLinearMap
      ((_root_.FiberBundle.trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
        (_root_.FiberBundle.mem_baseSet_trivializationAt F₂ E₂ x)).toLinearMap)
    (instNormedAddCommGroupTensor 𝕜 F₁ F₂).toUniformSpace.toTopologicalSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorFiberTopology then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorFiberTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorFiberTopology ``Submission.Bundle.TensorProduct.tensorFiberTopology

private noncomputable def trivEquiv (x : B) :
    (E₁ x ⊗[𝕜] E₂ x) ≃ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
  TensorProduct.congr
    ((_root_.FiberBundle.trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
      (_root_.FiberBundle.mem_baseSet_trivializationAt F₁ E₁ x)).toLinearEquiv
    ((_root_.FiberBundle.trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
      (_root_.FiberBundle.mem_baseSet_trivializationAt F₂ E₂ x)).toLinearEquiv

run_cmd do
  let target := ``Submission.Bundle.TensorProduct.trivEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Bundle.TensorProduct.trivEquiv target :: scope.openDecls } }

instance tensorFiberTopology_isTopologicalAddGroup (x : B) :
    @IsTopologicalAddGroup (E₁ x ⊗[𝕜] E₂ x) (tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x) _ := by
  change @IsTopologicalAddGroup _ (TopologicalSpace.induced _ _) _
  exact topologicalAddGroup_induced _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorFiberTopology_isTopologicalAddGroup then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorFiberTopology_isTopologicalAddGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorFiberTopology_isTopologicalAddGroup ``Submission.Bundle.TensorProduct.tensorFiberTopology_isTopologicalAddGroup

instance tensorFiberTopology_continuousSMul (x : B) :
    @ContinuousSMul 𝕜 (E₁ x ⊗[𝕜] E₂ x) _ _
      (tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x) := by
  change @ContinuousSMul 𝕜 _ _ _ (TopologicalSpace.induced _ _)
  exact continuousSMul_induced _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorFiberTopology_continuousSMul then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorFiberTopology_continuousSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorFiberTopology_continuousSMul ``Submission.Bundle.TensorProduct.tensorFiberTopology_continuousSMul

instance tensorFiberTopology_t2Space (x : B) :
    @T2Space (E₁ x ⊗[𝕜] E₂ x) (tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x) := by
  let : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact T2Space.of_injective_continuous (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).injective <| by
    change @Continuous _ _ (TopologicalSpace.induced _ _) _ _
    exact continuous_induced_dom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorFiberTopology_t2Space then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorFiberTopology_t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorFiberTopology_t2Space ``Submission.Bundle.TensorProduct.tensorFiberTopology_t2Space

noncomputable def continuousLinearEquivAt (x : B) :
    letI := tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    (E₁ x ⊗[𝕜] E₂ x) ≃L[𝕜] (F₁ ⊗[𝕜] F₂) := by
  letI := tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact ⟨trivEquiv 𝕜 F₁ F₂ E₁ E₂ x,
    continuous_induced_dom,
    LinearMap.continuous_of_finiteDimensional
      (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).symm.toLinearMap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.continuousLinearEquivAt then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.continuousLinearEquivAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.continuousLinearEquivAt ``Submission.Bundle.TensorProduct.continuousLinearEquivAt

variable {𝕜 E₁ E₂}

def toModel (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    {x : B} (t : E₁ x ⊗[𝕜] E₂ x) : F₁ ⊗[𝕜] F₂ :=
  trivEquiv 𝕜 F₁ F₂ E₁ E₂ x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.toModel then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.toModel ``Submission.Bundle.TensorProduct.toModel

def fromModel (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    {x : B} (f : F₁ ⊗[𝕜] F₂) : E₁ x ⊗[𝕜] E₂ x :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).symm f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.fromModel then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.fromModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.fromModel ``Submission.Bundle.TensorProduct.fromModel

variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
variable {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_add {x : B} (t₁ t₂ : E₁ x ⊗[𝕜] E₂ x) :
    toModel F₁ F₂ (t₁ + t₂) = toModel F₁ F₂ t₁ + toModel F₁ F₂ t₂ :=
  map_add (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x) t₁ t₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.toModel_add then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.toModel_add"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.toModel_add ``Submission.Bundle.TensorProduct.toModel_add

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_smul {x : B} (c : 𝕜) (t : E₁ x ⊗[𝕜] E₂ x) :
    toModel F₁ F₂ (c • t) = c • toModel F₁ F₂ t :=
  map_smul (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x) c t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.toModel_smul then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.toModel_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.toModel_smul ``Submission.Bundle.TensorProduct.toModel_smul

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_zero {x : B} :
    toModel F₁ F₂ (0 : E₁ x ⊗[𝕜] E₂ x) = 0 :=
  map_zero (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.toModel_zero then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.toModel_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.toModel_zero ``Submission.Bundle.TensorProduct.toModel_zero

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem fromModel_toModel {x : B} (t : E₁ x ⊗[𝕜] E₂ x) :
    fromModel F₁ F₂ (toModel F₁ F₂ t) = t :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).symm_apply_apply t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.fromModel_toModel then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.fromModel_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.fromModel_toModel ``Submission.Bundle.TensorProduct.fromModel_toModel

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
@[simp]
theorem toModel_fromModel {x : B} (f : F₁ ⊗[𝕜] F₂) :
    toModel F₁ F₂ (fromModel F₁ F₂ (x := x) f : E₁ x ⊗[𝕜] E₂ x) = f :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).apply_symm_apply f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.toModel_fromModel then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.toModel_fromModel"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.toModel_fromModel ``Submission.Bundle.TensorProduct.toModel_fromModel

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂] in
theorem toModel_injective {x : B} :
    Function.Injective (fun t : E₁ x ⊗[𝕜] E₂ x => toModel F₁ F₂ t) :=
  (trivEquiv 𝕜 F₁ F₂ E₁ E₂ x).injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.toModel_injective then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.toModel_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.toModel_injective ``Submission.Bundle.TensorProduct.toModel_injective

end Bundle.TensorProduct

end TensorProductFiber

end
