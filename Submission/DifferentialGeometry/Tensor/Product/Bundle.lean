/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
import Submission.DifferentialGeometry.Tensor.Product.Pretrivialization
import Submission.DifferentialGeometry.Tensor.Product.Fiber

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Product

open scoped _root_.Topology
open scoped _root_.TensorProduct _root_.Submission.TensorProduct

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Topology
open scoped _root_.Bundle _root_.Submission.Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B]

section
section TensorFiberTopology


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

variable (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

variable (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

@[reducible] noncomputable def tensorFiberTopologicalSpace (x : B) :
    TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) := by
  classical
  letI : TopologicalSpace (F₁ ⊗[𝕜] F₂) := inferInstance
  let L₁ : E₁ x ≃L[𝕜] F₁ :=
    (_root_.FiberBundle.trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 x
      (_root_.FiberBundle.mem_baseSet_trivializationAt F₁ E₁ x)
  let L₂ : E₂ x ≃L[𝕜] F₂ :=
    (_root_.FiberBundle.trivializationAt F₂ E₂ x).continuousLinearEquivAt 𝕜 x
      (_root_.FiberBundle.mem_baseSet_trivializationAt F₂ E₂ x)
  exact TopologicalSpace.induced
    (fun t : E₁ x ⊗[𝕜] E₂ x =>
      TensorProduct.map L₁.toLinearMap L₂.toLinearMap t)
    inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `tensorFiberTopologicalSpace then
    throwError "Refusing to shadow existing declaration tensorFiberTopologicalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `tensorFiberTopologicalSpace ``Submission.tensorFiberTopologicalSpace

@[reducible] noncomputable def tensorFiberTopologicalSpaceInst
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type*) [TopologicalSpace B]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₁ : B → Type*) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
    [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type*) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
    (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
  tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `tensorFiberTopologicalSpaceInst then
    throwError "Refusing to shadow existing declaration tensorFiberTopologicalSpaceInst"
  Lean.modifyEnv fun env => Lean.addAlias env `tensorFiberTopologicalSpaceInst ``Submission.tensorFiberTopologicalSpaceInst

omit [FiniteDimensional 𝕜 F₂] in
theorem tensorFiberTopologicalSpaceInst_eq
    (x : B) :
    tensorFiberTopologicalSpaceInst 𝕜 B F₁ F₂ E₁ E₂ x =
      tensorFiberTopologicalSpace (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
        (E₁ := E₁) (E₂ := E₂) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `tensorFiberTopologicalSpaceInst_eq then
    throwError "Refusing to shadow existing declaration tensorFiberTopologicalSpaceInst_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `tensorFiberTopologicalSpaceInst_eq ``Submission.tensorFiberTopologicalSpaceInst_eq

end TensorFiberTopology
end

section

universe u𝕜 uB uF₁ uF₂ uE₁ uE₂
namespace Bundle.TensorProduct
open _root_.Bundle

open _root_.Bundle.Pretrivialization
open scoped _root_.Manifold

class TensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (_root_.Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (_root_.Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    Type (max uB (max (uE₁+1) (uE₂+1))) where
  (fiberTop : ∀ x : B, TopologicalSpace (E₁ x ⊗[𝕜] E₂ x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.TensorFiberTopologies then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.TensorFiberTopologies"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.TensorFiberTopologies ``Submission.Bundle.TensorProduct.TensorFiberTopologies

attribute [reducible, instance] TensorFiberTopologies.fiberTop

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
     [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    [VectorBundle 𝕜 F₂ E₂] [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

noncomputable instance instNormedAddCommGroupTensor :
    NormedAddCommGroup (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  refine NormedAddCommGroup.induced
    (𝓕 := (F₁ ⊗[𝕜] F₂) →+ (cDual 𝕜 F₁ →L[𝕜] F₂))
    (E := (F₁ ⊗[𝕜] F₂))
    (F := (cDual 𝕜 F₁ →L[𝕜] F₂))
    (f := e.toLinearMap.toAddMonoidHom)
    ?_
  exact e.injective

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.instNormedAddCommGroupTensor then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.instNormedAddCommGroupTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.instNormedAddCommGroupTensor ``Submission.Bundle.TensorProduct.instNormedAddCommGroupTensor

noncomputable instance instNormedSpaceModelTensor :
    NormedSpace 𝕜 (F₁ ⊗[𝕜] F₂) :=
by
  classical
  let e := clmEquiv (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂)
  refine NormedSpace.induced
    (F := (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂))
    (𝕜 := 𝕜)
    (E := (F₁ ⊗[𝕜] F₂))
    (G := (cDual 𝕜 F₁ →L[𝕜] F₂))
    e.toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.instNormedSpaceModelTensor then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.instNormedSpaceModelTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.instNormedSpaceModelTensor ``Submission.Bundle.TensorProduct.instNormedSpaceModelTensor

noncomputable instance tensorFiberTopologies
    (𝕜 : Type u𝕜) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    (B : Type uB) [TopologicalSpace B]
    (F₁ : Type uF₁) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
    (F₂ : Type uF₂) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
    (E₁ : B → Type uE₁) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
      [TopologicalSpace (_root_.Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
      [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    (E₂ : B → Type uE₂) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
      [TopologicalSpace (_root_.Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] :
    TensorFiberTopologies 𝕜 B F₁ F₂ E₁ E₂ :=
  ⟨fun x =>
    tensorFiberTopology (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorFiberTopologies then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorFiberTopologies"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorFiberTopologies ``Submission.Bundle.TensorProduct.tensorFiberTopologies

noncomputable def vectorPrebundle :
    @VectorPrebundle
      𝕜
      B
      (F₁ ⊗[𝕜] F₂)
      (fun x ↦ E₁ x ⊗[𝕜] E₂ x)
      _
      _
      _
      instNormedAddCommGroupTensor
      instNormedSpaceModelTensor
      _
      (fun x => tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) x)
      :=
  letI := tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂)
  {
    pretrivializationAtlas :=
      {e | ∃ (e₁ : _root_.Bundle.Trivialization F₁ (π F₁ E₁)) (e₂ : _root_.Bundle.Trivialization F₂ (π F₂ E₂))
        (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
          e = Pretrivialization.tensorProduct (𝕜 := 𝕜) e₁ e₂}
    pretrivialization_linear' := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
      apply Pretrivialization.tensorProduct.isLinear
    pretrivializationAt := fun x =>
      Pretrivialization.tensorProduct (𝕜 := 𝕜) (_root_.FiberBundle.trivializationAt F₁ E₁ x) (_root_.FiberBundle.trivializationAt F₂ E₂ x)
    mem_base_pretrivializationAt := fun x =>
      ⟨mem_baseSet_trivializationAt F₁ E₁ x, _root_.FiberBundle.mem_baseSet_trivializationAt F₂ E₂ x⟩
    pretrivialization_mem_atlas := fun x =>
      ⟨trivializationAt F₁ E₁ x, _root_.FiberBundle.trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
    exists_coordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      refine ⟨Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) (e₁ := e₁) (e₁' := e₁')
                (e₂ := e₂) (e₂' := e₂'),
              ?_, Pretrivialization.tensorProductCoordChange_apply (𝕜 := 𝕜)
                (e₁ := e₁) (e₁' := e₁') (e₂ := e₂) (e₂' := e₂')⟩
      change ContinuousOn
        (Pretrivialization.tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂')
        (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
      exact Pretrivialization.continuousOn_tensorProductCoordChange (𝕜 := 𝕜)
    totalSpaceMk_isInducing := by
      intro b
      let : TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
         tensorFiberTopology (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂) (E₁:=E₁) (E₂:=E₂) b
      let L₁ : E₁ b ≃L[𝕜] F₁ :=
        (_root_.FiberBundle.trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜 b
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ _)
      let L₂ : E₂ b ≃L[𝕜] F₂ :=
        (_root_.FiberBundle.trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜 b
          (_root_.FiberBundle.mem_baseSet_trivializationAt _ _ _)
      have hind : _root_.Topology.IsInducing (TensorProduct.map L₁.toLinearMap L₂.toLinearMap) := ⟨rfl⟩
      have : _root_.Topology.IsInducing fun x ↦ (b, TensorProduct.map L₁.toLinearMap L₂.toLinearMap x) :=
        isInducing_const_prod.mpr hind
      convert this using 1
      funext x
      simp only [Function.comp_apply, Pretrivialization.tensorProduct_apply,
                  Prod.mk.injEq, true_and]
      have hL1 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (_root_.FiberBundle.trivializationAt F₁ E₁ b) b) :
              E₁ b →ₗ[𝕜] F₁) =
            (↑L₁.toLinearEquiv : E₁ b →ₗ[𝕜] F₁) := by
        ext w
        simpa [L₁] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (_root_.FiberBundle.trivializationAt F₁ E₁ b)
              (_root_.FiberBundle.mem_baseSet_trivializationAt F₁ E₁ b)).symm
      have hL2 :
          (↑(Trivialization.continuousLinearMapAt 𝕜 (_root_.FiberBundle.trivializationAt F₂ E₂ b) b) :
              E₂ b →ₗ[𝕜] F₂) =
            (↑L₂.toLinearEquiv : E₂ b →ₗ[𝕜] F₂) := by
        ext w
        simpa [L₂] using
          congrArg (fun f => f w)
            (Trivialization.coe_continuousLinearEquivAt_eq (R := 𝕜)
              (_root_.FiberBundle.trivializationAt F₂ E₂ b)
              (_root_.FiberBundle.mem_baseSet_trivializationAt F₂ E₂ b)).symm
      simp [hL1, hL2]
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.vectorPrebundle then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.vectorPrebundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.vectorPrebundle ``Submission.Bundle.TensorProduct.vectorPrebundle

noncomputable instance topologicalSpaceTotalSpace :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) x
  exact
    (Bundle.TensorProduct.vectorPrebundle
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.topologicalSpaceTotalSpace then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.topologicalSpaceTotalSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.topologicalSpaceTotalSpace ``Submission.Bundle.TensorProduct.topologicalSpaceTotalSpace

@[reducible] noncomputable def tensorFiberTop :
    (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
  fun b =>
    Bundle.TensorProduct.tensorFiberTopology
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorFiberTop then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorFiberTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorFiberTop ``Submission.Bundle.TensorProduct.tensorFiberTop

@[reducible] noncomputable def tensorTotalSpaceTop :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (F₁ ⊗[𝕜] F₂) (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)) :=
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).totalSpaceTopology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorTotalSpaceTop then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorTotalSpaceTop"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorTotalSpaceTop ``Submission.Bundle.TensorProduct.tensorTotalSpaceTop
attribute [local instance] tensorTotalSpaceTop

noncomputable instance fiberBundle :
    @FiberBundle
      B
      (F₁ ⊗[𝕜] F₂)
      inferInstance
      inferInstance
      (fun x : B ↦ E₁ x ⊗[𝕜] E₂ x)
      (tensorTotalSpaceTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂))
      (tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)) := by
  classical
  letI : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toFiberBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.fiberBundle then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.fiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.fiberBundle ``Submission.Bundle.TensorProduct.fiberBundle
attribute [local instance] fiberBundle

noncomputable instance vectorBundle :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop
        (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    VectorBundle 𝕜 (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) := by
  classical
  let : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).toVectorBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.vectorBundle then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.vectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.vectorBundle ``Submission.Bundle.TensorProduct.vectorBundle

variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂]

open _root_.Bundle _root_.Bundle.Trivialization in
noncomputable def _root_.Submission.Bundle.Trivialization.tensorProduct :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) := by
  classical
  letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
  exact
    VectorPrebundle.trivializationOfMemPretrivializationAtlas _
      ⟨e₁, e₂, he₁, he₂, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.Trivialization.tensorProduct then
    throwError "Refusing to shadow existing declaration Bundle.Trivialization.tensorProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.Trivialization.tensorProduct ``Submission.Bundle.Trivialization.tensorProduct

noncomputable instance memTrivializationAtlas :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    MemTrivializationAtlas
      (e₁.tensorProduct (𝕜 := 𝕜) e₂ :
        Trivialization (F₁ ⊗[𝕜] F₂) (π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x))) := by
  let : (b : B) → TopologicalSpace (E₁ b ⊗[𝕜] E₂ b) := fun b ↦ inferInstance
  exact ⟨_, ⟨e₁, e₂, he₁, he₂, rfl⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.memTrivializationAtlas then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.memTrivializationAtlas"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.memTrivializationAtlas ``Submission.Bundle.TensorProduct.memTrivializationAtlas

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
@[simp]
theorem _root_.Submission.Trivialization.baseSet_tensorProduct :
    (e₁.tensorProduct (𝕜 := 𝕜) e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Trivialization
  let env ← Lean.getEnv
  if env.contains `Trivialization.baseSet_tensorProduct then
    throwError "Refusing to shadow existing declaration Trivialization.baseSet_tensorProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `Trivialization.baseSet_tensorProduct ``Submission.Trivialization.baseSet_tensorProduct

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
theorem _root_.Submission.Trivialization.tensorProduct_apply
    (p : _root_.Bundle.TotalSpace (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x)) :
    e₁.tensorProduct (𝕜 := 𝕜) e₂ p =
      ⟨p.1, TensorProduct.map
        (e₁.continuousLinearMapAt 𝕜 p.1).toLinearMap
        (e₂.continuousLinearMapAt 𝕜 p.1).toLinearMap p.2⟩ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Trivialization.tensorProduct_apply then
    throwError "Refusing to shadow existing declaration Trivialization.tensorProduct_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Trivialization.tensorProduct_apply ``Submission.Trivialization.tensorProduct_apply

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
theorem tensorProduct_trivializationAt (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    _root_.FiberBundle.trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀ =
      (_root_.FiberBundle.trivializationAt F₁ E₁ x₀).tensorProduct (𝕜 := 𝕜) (_root_.FiberBundle.trivializationAt F₂ E₂ x₀) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorProduct_trivializationAt then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorProduct_trivializationAt"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorProduct_trivializationAt ``Submission.Bundle.TensorProduct.tensorProduct_trivializationAt

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_source (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (_root_.FiberBundle.trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).source =
      π (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) ⁻¹'
        ((_root_.FiberBundle.trivializationAt F₁ E₁ x₀).baseSet ∩ (_root_.FiberBundle.trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorProduct_trivializationAt_source then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorProduct_trivializationAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorProduct_trivializationAt_source ``Submission.Bundle.TensorProduct.tensorProduct_trivializationAt_source

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
@[simp, mfld_simps]
theorem tensorProduct_trivializationAt_target (x₀ : B) :
      letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (_root_.FiberBundle.trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).target =
      ((_root_.FiberBundle.trivializationAt F₁ E₁ x₀).baseSet ∩ (_root_.FiberBundle.trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorProduct_trivializationAt_target then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorProduct_trivializationAt_target"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorProduct_trivializationAt_target ``Submission.Bundle.TensorProduct.tensorProduct_trivializationAt_target

omit [∀ x, ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
@[simp]
theorem tensorProduct_trivializationAt_baseSet (x₀ : B) :
    letI : (x : B) → TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      tensorFiberTop (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)
    (_root_.FiberBundle.trivializationAt (F₁ ⊗[𝕜] F₂) (fun x ↦ E₁ x ⊗[𝕜] E₂ x) x₀).baseSet =
      ((_root_.FiberBundle.trivializationAt F₁ E₁ x₀).baseSet ∩ (_root_.FiberBundle.trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.tensorProduct_trivializationAt_baseSet then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.tensorProduct_trivializationAt_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.tensorProduct_trivializationAt_baseSet ``Submission.Bundle.TensorProduct.tensorProduct_trivializationAt_baseSet

end Bundle.TensorProduct

end


open scoped _root_.Manifold

section Smooth

open _root_.Submission.Pretrivialization _root_.Bundle.Pretrivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
variable (n : WithTop ℕ∞)
variable [∀ (x : B), ContinuousAdd (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
variable [∀ (x : B), ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
variable [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

instance Bundle.TensorProduct.vectorPrebundle.isContMDiff :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    (Bundle.TensorProduct.vectorPrebundle
      (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂)).IsContMDiff IB n := by
  let (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact {
    exists_contMDiffCoordChange := by
      rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
      have := he₁; have := he₂; have := he₁'; have := he₂'
      refine ⟨tensorProductCoordChange (𝕜 := 𝕜) e₁ e₁' e₂ e₂',
        contMDiffOn_tensorProductCoordChange IB n, ?_⟩
      rintro b hb v
      exact tensorProductCoordChange_apply (𝕜 := 𝕜) e₁ e₁' e₂ e₂' b hb v
  }

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.Bundle.TensorProduct.vectorPrebundle
  let env ← Lean.getEnv
  if env.contains `Bundle.TensorProduct.vectorPrebundle.isContMDiff then
    throwError "Refusing to shadow existing declaration Bundle.TensorProduct.vectorPrebundle.isContMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.TensorProduct.vectorPrebundle.isContMDiff ``Submission.Bundle.TensorProduct.vectorPrebundle.isContMDiff

open _root_.ContMDiffVectorBundle in
instance ContMDiffVectorBundle.tensorProduct :
    letI (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
      Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
    ContMDiffVectorBundle n (F₁ ⊗[𝕜] F₂) (fun x => E₁ x ⊗[𝕜] E₂ x) IB := by
  let (x : B) : TopologicalSpace (E₁ x ⊗[𝕜] E₂ x) :=
    Bundle.TensorProduct.tensorFiberTopology 𝕜 F₁ F₂ E₁ E₂ x
  exact (Bundle.TensorProduct.vectorPrebundle
    (𝕜 := 𝕜) (B := B) (F₁ := F₁) (F₂ := F₂)
    (E₁ := E₁) (E₂ := E₂)).contMDiffVectorBundle IB

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.ContMDiffVectorBundle
  let env ← Lean.getEnv
  if env.contains `ContMDiffVectorBundle.tensorProduct then
    throwError "Refusing to shadow existing declaration ContMDiffVectorBundle.tensorProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `ContMDiffVectorBundle.tensorProduct ``Submission.ContMDiffVectorBundle.tensorProduct

end Smooth
