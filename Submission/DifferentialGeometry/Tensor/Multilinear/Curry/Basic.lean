/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Tensor.Multilinear

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

noncomputable def continuousMultilinearMapCurryEquiv (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 F 𝕜 finSumFinEquiv.symm).trans
    (ContinuousMultilinearMap.currySumEquiv 𝕜 (Fin r) (Fin r') F 𝕜)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryEquiv ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryEquiv

noncomputable def continuousMultilinearMapCurryLeft (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) :=
  (continuousMultilinearMapCurryEquiv r r' (𝕜 := 𝕜) (F := F)).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryLeft ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapCurryLeft

noncomputable def continuousMultilinearMapUncurryLeft (r r' : ℕ) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜) →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜 :=
  (continuousMultilinearMapCurryEquiv r r' (𝕜 := 𝕜) (F := F)).symm.toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapUncurryLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapUncurryLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapUncurryLeft ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMapUncurryLeft

@[simp]
theorem continuousMultilinearMap_curryLeft_uncurryLeft (r r' : ℕ)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r' => F) 𝕜)) :
    (continuousMultilinearMapCurryLeft (𝕜 := 𝕜) (F := F) r r')
      ((continuousMultilinearMapUncurryLeft (𝕜 := 𝕜) (F := F) r r') g) = g := by
  simp [continuousMultilinearMapCurryLeft, continuousMultilinearMapUncurryLeft]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_curryLeft_uncurryLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_curryLeft_uncurryLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_curryLeft_uncurryLeft ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_curryLeft_uncurryLeft

@[simp]
theorem continuousMultilinearMap_uncurryLeft_curryLeft (r r' : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (r + r') => F) 𝕜) :
    (continuousMultilinearMapUncurryLeft (𝕜 := 𝕜) (F := F) r r')
      ((continuousMultilinearMapCurryLeft (𝕜 := 𝕜) (F := F) r r') f) = f := by
  simp only [continuousMultilinearMapCurryLeft, continuousMultilinearMapUncurryLeft]
  exact (continuousMultilinearMapCurryEquiv r r').toContinuousLinearEquiv.symm_apply_apply f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_uncurryLeft_curryLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_uncurryLeft_curryLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_uncurryLeft_curryLeft ``Submission.DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_uncurryLeft_curryLeft

end

end DifferentialGeometry.Tensor.Multilinear
