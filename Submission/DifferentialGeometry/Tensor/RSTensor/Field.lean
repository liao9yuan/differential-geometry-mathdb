/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Alternating.Composition
import Submission.DifferentialGeometry.Tensor.Multilinear.Composition
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Submission.DifferentialGeometry.Tensor.Multilinear.Smoothness.LinearIsometry
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Submission.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.BundleBasis
import Submission.DifferentialGeometry.Tensor.Product.Defs
import Submission.DifferentialGeometry.Tensor.Product.HomEquiv
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Submission.DifferentialGeometry.Tensor.Alternating.Curry
import Submission.DifferentialGeometry.Tensor.Alternating.Flip
import Submission.DifferentialGeometry.Tensor.Multilinear.Flip
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Mul
import Submission.DifferentialGeometry.Tensor.Alternating.Reindexing.Domain
import Mathlib.LinearAlgebra.Alternating.Basic
import Submission.DifferentialGeometry.Tensor.Alternating.Shuffle.Decomposition
import Submission.DifferentialGeometry.Tensor.Alternating.Shuffle.Split
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Group
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Cases
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import Submission.DifferentialGeometry.Tensor.Product.Basis
import Submission.DifferentialGeometry.Tensor.Product.Bundle
import Submission.DifferentialGeometry.Tensor.Product.Pretrivialization
import Mathlib.Topology.FiberBundle.Basic
import Submission.DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry
namespace Tensor0SBundle
noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

section ApplyInput

variable {r s : ℕ} [CompleteSpace 𝕜]

noncomputable def modelApplyInputBilinear (r s : ℕ) :
    Tensor0SModel r 𝕜 E →L[𝕜]
      (TensorRSModel r s 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (ContinuousLinearMap.id 𝕜 (TensorRSModel r s 𝕜 E))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.modelApplyInputBilinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.modelApplyInputBilinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.modelApplyInputBilinear ``Submission.DifferentialGeometry.Tensor0SBundle.modelApplyInputBilinear

omit [CompleteSpace 𝕜] in
@[simp]
theorem model_applyInput_bilinear_apply (r s : ℕ)
    (θ : Tensor0SModel r 𝕜 E) (T : TensorRSModel r s 𝕜 E) :
    modelApplyInputBilinear (𝕜 := 𝕜) (E := E) r s θ T = T θ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.model_applyInput_bilinear_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.model_applyInput_bilinear_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.model_applyInput_bilinear_apply ``Submission.DifferentialGeometry.Tensor0SBundle.model_applyInput_bilinear_apply

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_applyInput_eq
    (r s : ℕ) {x₀ x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (θ : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x) :
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
    letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    ((_root_.FiberBundle.trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀) ⟨x, T θ⟩).2 =
      (((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀) ⟨x, T⟩).2)
        (((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  let := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ext v
  rw [Tensor0SSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) s]
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) r s hx]
  have hθ :
      (_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x
        (((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2) = θ := by
    have hcoord :
        (_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).continuousLinearMapAt 𝕜 x θ =
          ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
            (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ⟩).2 := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      exact congrFun ((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx) θ
    rw [← hcoord]
    exact (_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx θ
  rw [hθ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensor0SModelAt_applyInput_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensor0SModelAt_applyInput_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensor0SModelAt_applyInput_eq ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0SModelAt_applyInput_eq

noncomputable def tensorRSFieldApplyInputFun
    (T : (x : M) ->
      TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (θ : (x : M) ->
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x) :
    (x : M) ->
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x :=
  fun x => T x (θ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInputFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInputFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInputFun ``Submission.DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInputFun

noncomputable def tensorRSFieldApplyInput
    (T : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (θ : Tensor0SField n r (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨tensorRSFieldApplyInputFun (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) (r := r) (s := s) (fun x => T x) (fun x => θ x), ?_⟩
  intro x₀
  rw [_root_.Bundle.contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [_root_.Bundle.contMDiffAt_section] at hT
  have hθ := θ.contMDiff x₀
  rw [_root_.Bundle.contMDiffAt_section] at hθ
  have hcombine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x : M =>
          modelApplyInputBilinear (𝕜 := 𝕜) (E := E) r s
            (((_root_.FiberBundle.trivializationAt (Tensor0SModel r 𝕜 E)
                (fun x => Tensor0SSpace r I x) x₀) ⟨x, θ x⟩).2)
            (((_root_.FiberBundle.trivializationAt (TensorRSModel r s 𝕜 E)
                (fun x => TensorRSSpace r s I x) x₀) ⟨x, T x⟩).2)) x₀ := by
    exact ((contMDiffAt_const
      (c := modelApplyInputBilinear (𝕜 := 𝕜) (E := E) r s)).clm_apply hθ).clm_apply hT
  refine hcombine.congr_of_eventuallyEq ?_
  filter_upwards
    [(_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
  exact tensor0SModelAt_applyInput_eq (𝕜 := 𝕜) (E := E) (I := I)
    (M := M) r s hx (T x) (θ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInput ``Submission.DifferentialGeometry.Tensor0SBundle.tensorRSFieldApplyInput

omit [IsManifold I (n + 1) M] in
omit [CompleteSpace 𝕜] in
@[simp]
theorem tensorRSField_applyInput_apply
    (T : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (θ : Tensor0SField n r (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    tensorRSFieldApplyInput (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n T θ x = T x (θ x) := by
  unfold tensorRSFieldApplyInput
  change tensorRSFieldApplyInputFun (fun x => T x) (fun x => θ x) x = T x (θ x)
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensorRSField_applyInput_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensorRSField_applyInput_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensorRSField_applyInput_apply ``Submission.DifferentialGeometry.Tensor0SBundle.tensorRSField_applyInput_apply

end ApplyInput

section SmulByFun

variable {r s : ℕ} [CompleteSpace 𝕜]

end SmulByFun

noncomputable def Tensor0SField.one0 [CompleteSpace 𝕜] :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  Tensor0SField.fromScalarField n (fun _ : M => (1 : 𝕜)) contMDiff_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0 ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0

omit [IsManifold I (n + 1) M] in
@[simp]
theorem Tensor0SField.one0_apply [CompleteSpace 𝕜]
    (x : M) (v : Fin 0 → E) :
    Tensor0SField.one0 (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) n x v = (1 : 𝕜) := by
  exact Tensor0SField.fromScalarField_apply n (fun _ : M => (1 : 𝕜))
    contMDiff_const x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0_apply ``Submission.DifferentialGeometry.Tensor0SBundle.Tensor0SField.one0_apply

end
end Tensor0SBundle

namespace Tensor0SBundle
noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap

open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
variable {s q : ℕ}

variable (n : WithTop ℕ∞)

end
end Tensor0SBundle
end DifferentialGeometry
