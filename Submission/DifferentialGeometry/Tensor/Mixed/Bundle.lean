/-
Authors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Mixed.Fiber
import Mathlib.Geometry.Manifold.VectorBundle.Hom

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap

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

noncomputable instance mixedTopology (r s : ℕ) :
    TopologicalSpace (_root_.Bundle.TotalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedTopology then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedTopology ``Submission.Bundle.continuousMultilinearMap.mixedTopology

noncomputable instance mixedFiberBundle (r s : ℕ) :
    @FiberBundle B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      _ (by infer_instance : TopologicalSpace _)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      (mixedTopology r s) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedFiberBundle then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedFiberBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedFiberBundle ``Submission.Bundle.continuousMultilinearMap.mixedFiberBundle

noncomputable instance mixedVectorBundle (r s : ℕ) :
    @VectorBundle 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      _
      (fun x => by infer_instance) (fun x => by infer_instance)
      inferInstance inferInstance _
      (mixedTopology r s) _
      (mixedFiberBundle r s) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 r F E x)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedVectorBundle then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedVectorBundle ``Submission.Bundle.continuousMultilinearMap.mixedVectorBundle

section smooth

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable (IB : ModelWithCorners 𝕜 EB HB)
variable [ChartedSpace HB B]
variable (n : WithTop ℕ∞)
variable [ContMDiffVectorBundle n F E IB]

noncomputable instance mixedSmoothVectorBundle (r s : ℕ) :
    @ContMDiffVectorBundle n 𝕜 B
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (fun x : B => Bundle.continuousMultilinearMap 𝕜 r F E x →L[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 s F E x)
      _ EB _ _ HB _ IB _ _ _ _ _ _
      (mixedTopology r s) _
      (mixedFiberBundle r s)
      (mixedVectorBundle r s) :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Bundle.continuousMultilinearMap.mixedSmoothVectorBundle then
    throwError "Refusing to shadow existing declaration Bundle.continuousMultilinearMap.mixedSmoothVectorBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `Bundle.continuousMultilinearMap.mixedSmoothVectorBundle ``Submission.Bundle.continuousMultilinearMap.mixedSmoothVectorBundle

end smooth

end Bundle.continuousMultilinearMap

end
