/-
Authors: Yuan Liao, Jack McCarthy
-/
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Tensor.Product

open scoped _root_.Topology _root_.TensorProduct

noncomputable section

section TensorNorm

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
variable (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

omit [FiniteDimensional 𝕜 F₂] in
noncomputable def tensorHomEquiv : (F₁ ⊗[𝕜] F₂) ≃ₗ[𝕜] ((Module.Dual 𝕜 F₁) →ₗ[𝕜] F₂) := by
  let f : Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ≃ₗ[𝕜] F₁ := (Module.evalEquiv 𝕜 F₁).symm
  have h₀ : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁)) ⊗[𝕜] F₂ ≃ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
    let g : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) →ₗ[𝕜] (F₁ ⊗[𝕜] F₂) :=
      TensorProduct.lift ((TensorProduct.mk 𝕜 F₁ F₂) ∘ₗ f.toLinearMap)
    let ginv : (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) :=
      TensorProduct.lift
        ((TensorProduct.mk 𝕜 (Module.Dual 𝕜 (Module.Dual 𝕜 F₁)) F₂) ∘ₗ f.symm.toLinearMap)
    have left_inv₀ : ginv ∘ₗ g = LinearMap.id := by
      ext v w
      unfold ginv g
      simp
    have left_inv : ∀ x, ginv (g x) = x := by
      intro x
      rw [←@Function.comp_apply _ _ _ ginv g x]
      have h : (ginv ∘ₗ g : (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂) →
        (Module.Dual 𝕜 (Module.Dual 𝕜 F₁) ⊗[𝕜] F₂)) = ginv ∘ g := by simp
      rw [←h, left_inv₀]
      simp
    have right_inv₀ : g ∘ₗ ginv = LinearMap.id := by
      ext v w
      unfold ginv g
      simp
    have right_inv : ∀ x, g (ginv x) = x := by
      intro x
      rw [←@Function.comp_apply _ _ _ g ginv x]
      have h : (g ∘ₗ ginv : (F₁ ⊗[𝕜] F₂) → (F₁ ⊗[𝕜] F₂)) = g ∘ ginv := by simp
      rw [←h, right_inv₀]
      simp
    LinearEquiv.mk g ginv left_inv right_inv
  have h₁ := (dualTensorHomEquiv 𝕜 (Module.Dual 𝕜 F₁) F₂)
  exact LinearEquiv.trans (LinearEquiv.symm h₀) h₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Product.tensorHomEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.tensorHomEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.tensorHomEquiv ``Submission.DifferentialGeometry.Tensor.Product.tensorHomEquiv

abbrev cDual := F₁ →L[𝕜] 𝕜

private noncomputable def pureTensorToHom :
    F₁ →ₗ[𝕜] F₂ →ₗ[𝕜] (cDual (𝕜:=𝕜) (F₁:=F₁) →L[𝕜] F₂) :=
by
  classical
  refine
    { toFun := fun v =>
        { toFun := fun w =>
            ({
              toFun := fun φ => (φ v) • w
              map_add' := by
                intro φ ψ
                simp [add_smul]
              map_smul' := by
                intro a φ
                simp [_root_.SemigroupAction.mul_smul]
            } : (cDual (𝕜:=𝕜) (F₁:=F₁) →ₗ[𝕜] F₂)).toContinuousLinearMap
          map_add' := by
            intro w₁ w₂
            ext φ
            simp [smul_add]
          map_smul' := by
            intro a w
            ext φ
            simp [smul_smul, mul_comm] }
      map_add' := by
        intro v₁ v₂
        ext w φ
        simp [add_smul]
      map_smul' := by
        intro a v
        ext w φ
        simp [_root_.SemigroupAction.mul_smul] }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Product.pureTensorToHom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Product.pureTensorToHom target :: scope.openDecls } }

noncomputable def toHom :
    (F₁ ⊗[𝕜] F₂) →ₗ[𝕜] (cDual (𝕜:=𝕜) (F₁:=F₁) →L[𝕜] F₂) :=
_root_.TensorProduct.lift (pureTensorToHom (𝕜:=𝕜) (F₁:=F₁) (F₂:=F₂))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Product.toHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.toHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.toHom ``Submission.DifferentialGeometry.Tensor.Product.toHom

omit [FiniteDimensional 𝕜 F₂]

lemma finrank_continuousLinearMap :
    Module.finrank 𝕜 (F₁ →L[𝕜] F₂) = Module.finrank 𝕜 F₁ * Module.finrank 𝕜 F₂ := by
  have : Module.Free 𝕜 F₁ := inferInstance
  have : Module.Free 𝕜 F₂ := inferInstance
  have e : (F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  rw [e.finrank_eq]
  rw [Module.finrank_linearMap 𝕜 𝕜]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Product.finrank_continuousLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.finrank_continuousLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.finrank_continuousLinearMap ``Submission.DifferentialGeometry.Tensor.Product.finrank_continuousLinearMap

def cDualEqivDual : cDual 𝕜 F₁ ≃ₗ[𝕜] Module.Dual 𝕜 F₁ := by
  unfold cDual Module.Dual
  exact (@LinearMap.toContinuousLinearMap 𝕜 _ F₁ _ _ _ _ _ 𝕜 _ _ _ _ _ _ _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Product.cDualEqivDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.cDualEqivDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.cDualEqivDual ``Submission.DifferentialGeometry.Tensor.Product.cDualEqivDual

def cDualClmEquivDualLm : (cDual 𝕜 F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (Module.Dual 𝕜 F₁ →ₗ[𝕜] F₂) := by
  have e : (cDual 𝕜 F₁ →L[𝕜] F₂) ≃ₗ[𝕜] (cDual 𝕜 F₁ →ₗ[𝕜] F₂) := LinearMap.toContinuousLinearMap.symm
  have e' : (cDual 𝕜 F₁ →ₗ[𝕜] F₂) ≃ₗ[𝕜] (Module.Dual 𝕜 F₁ →ₗ[𝕜] F₂) :=
    LinearEquiv.congrLeft F₂ 𝕜 (cDualEqivDual 𝕜 F₁)
  exact LinearEquiv.trans e e'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Product.cDualClmEquivDualLm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.cDualClmEquivDualLm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.cDualClmEquivDualLm ``Submission.DifferentialGeometry.Tensor.Product.cDualClmEquivDualLm

noncomputable def clmEquiv : (F₁ ⊗[𝕜] F₂) ≃ₗ[𝕜] (cDual 𝕜 F₁ →L[𝕜] F₂) :=
  LinearEquiv.trans (tensorHomEquiv 𝕜 F₁ F₂) (cDualClmEquivDualLm 𝕜 F₁ F₂).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Product.clmEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.clmEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.clmEquiv ``Submission.DifferentialGeometry.Tensor.Product.clmEquiv

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
  if env.contains `DifferentialGeometry.Tensor.Product.instNormedAddCommGroupTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.instNormedAddCommGroupTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.instNormedAddCommGroupTensor ``Submission.DifferentialGeometry.Tensor.Product.instNormedAddCommGroupTensor

noncomputable instance instNormedSpaceTensor :
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
  if env.contains `DifferentialGeometry.Tensor.Product.instNormedSpaceTensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Product.instNormedSpaceTensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Product.instNormedSpaceTensor ``Submission.DifferentialGeometry.Tensor.Product.instNormedSpaceTensor

end TensorNorm

end

end DifferentialGeometry.Tensor.Product
