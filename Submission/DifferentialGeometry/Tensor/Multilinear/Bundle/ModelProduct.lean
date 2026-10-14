/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle

open scoped _root_.TensorProduct _root_.Submission.TensorProduct _root_.Submission.Bundle.TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

def modelProductₗ (s q : ℕ) :
    (MLF s) →ₗ[𝕜] (MLF q) →ₗ[𝕜] (MLF (s + q)) :=
  LinearMap.mk₂ 𝕜 (modelProduct (𝕜 := 𝕜) (F := F) s q)
    (fun f₁ f₂ g => by ext v; simp [modelProduct_apply, add_mul])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)
    (fun f g₁ g₂ => by ext v; simp [modelProduct_apply, mul_add])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.modelProductₗ then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.modelProductₗ"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.modelProductₗ ``Submission.Bundle.continuousMultilinearMap.modelProductₗ

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
@[simp]
theorem modelProductₗ_apply (s q : ℕ)
    (f : MLF s) (g : MLF q) :
    modelProductₗ (𝕜 := 𝕜) (F := F) s q f g = modelProduct s q f g :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.modelProductₗ_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.modelProductₗ_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.modelProductₗ_apply ``Submission.Bundle.continuousMultilinearMap.modelProductₗ_apply

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem modelProduct_norm_bound (s q : ℕ) (f : MLF s) (g : MLF q) :
    ‖modelProduct (𝕜 := 𝕜) (F := F) s q f g‖ ≤ 1 * ‖f‖ * ‖g‖ := by
  rw [one_mul]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v => ?_)
  rw [modelProduct_apply, norm_mul]
  calc ‖f (v ∘ Fin.castAdd q)‖ * ‖g (v ∘ Fin.natAdd s)‖
      ≤ (‖f‖ * ∏ i, ‖(v ∘ Fin.castAdd q) i‖) * (‖g‖ * ∏ i, ‖(v ∘ Fin.natAdd s) i‖) := by
        gcongr
        · exact f.le_opNorm _
        · exact g.le_opNorm _
    _ = ‖f‖ * ‖g‖ * ∏ i, ‖v i‖ := by
        rw [Fin.prod_univ_add (fun i => ‖v i‖)]
        simp only [Function.comp_apply]
        ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.modelProduct_norm_bound then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.modelProduct_norm_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.modelProduct_norm_bound ``Submission.Bundle.continuousMultilinearMap.modelProduct_norm_bound

def modelProductL (s q : ℕ) :
    (MLF s) →L[𝕜] (MLF q) →L[𝕜] (MLF (s + q)) :=
  LinearMap.mkContinuous₂ (modelProductₗ (𝕜 := 𝕜) (F := F) s q) 1
    (fun f g => modelProduct_norm_bound s q f g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.modelProductL then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.modelProductL"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.modelProductL ``Submission.Bundle.continuousMultilinearMap.modelProductL

omit [CompleteSpace 𝕜] in
@[simp]
theorem modelProductL_apply (s q : ℕ)
    (f : MLF s) (g : MLF q) :
    modelProductL (𝕜 := 𝕜) (F := F) s q f g = modelProduct s q f g :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.modelProductL_apply then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.modelProductL_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.modelProductL_apply ``Submission.Bundle.continuousMultilinearMap.modelProductL_apply

omit [CompleteSpace 𝕜] in
theorem isBoundedBilinearMap_modelProduct (s q : ℕ) :
    IsBoundedBilinearMap 𝕜
      (fun p : (MLF s) × (MLF q) => modelProduct (𝕜 := 𝕜) (F := F) s q p.1 p.2) :=
  (modelProductL (𝕜 := 𝕜) (F := F) s q).isBoundedBilinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.isBoundedBilinearMap_modelProduct then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.isBoundedBilinearMap_modelProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.isBoundedBilinearMap_modelProduct ``Submission.Bundle.continuousMultilinearMap.isBoundedBilinearMap_modelProduct

omit [CompleteSpace 𝕜] in
theorem hasFDerivAt_modelProduct {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (s q : ℕ) {f : X → MLF s} {g : X → MLF q}
    {f' : X →L[𝕜] (MLF s)} {g' : X →L[𝕜] (MLF q)} {x : X}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => modelProduct (𝕜 := 𝕜) (F := F) s q (f y) (g y))
      ((modelProductL (𝕜 := 𝕜) (F := F) s q).precompR X (f x) g'
        + (modelProductL (𝕜 := 𝕜) (F := F) s q).precompL X f' (g x)) x := by
  simp only [← modelProductL_apply]
  fun_prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.hasFDerivAt_modelProduct then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.hasFDerivAt_modelProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.hasFDerivAt_modelProduct ``Submission.Bundle.continuousMultilinearMap.hasFDerivAt_modelProduct

end Bundle.continuousMultilinearMap
