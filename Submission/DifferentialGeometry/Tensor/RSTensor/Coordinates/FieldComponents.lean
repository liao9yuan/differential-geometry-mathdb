import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.Expansion
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
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
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Section
import Submission.DifferentialGeometry.Tensor.Product.Basis
import Submission.DifferentialGeometry.Tensor.Product.Bundle
import Submission.DifferentialGeometry.Tensor.Product.Pretrivialization
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
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
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
import Mathlib.Topology.FiberBundle.Basic
import Submission.DifferentialGeometry.Tensor.Product.Fiber
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Submission.DifferentialGeometry.Bundle.Section

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor0SBundle

open _root_.Bundle _root_.Submission.Bundle _root_.Module
open scoped _root_.Manifold _root_.BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

section Covariant

variable {s q : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_add_field
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A + B) slots =
      component0S (I := I) basis A slots + component0S (I := I) basis B slots := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.component0S_add_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.component0S_add_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.component0S_add_field ``Submission.DifferentialGeometry.Tensor0SBundle.component0S_add_field

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_neg_field
    (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (-A) slots =
      -component0S (I := I) basis A slots := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.component0S_neg_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.component0S_neg_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.component0S_neg_field ``Submission.DifferentialGeometry.Tensor0SBundle.component0S_neg_field

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_sub_field
    (A B : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (A - B) slots =
      component0S (I := I) basis A slots - component0S (I := I) basis B slots := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.component0S_sub_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.component0S_sub_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.component0S_sub_field ``Submission.DifferentialGeometry.Tensor0SBundle.component0S_sub_field

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_smul_field
    (c : 𝕜) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (c • A) slots =
      c * component0S (I := I) basis A slots := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.component0S_smul_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.component0S_smul_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.component0S_smul_field ``Submission.DifferentialGeometry.Tensor0SBundle.component0S_smul_field

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_nsmul
    (n : ℕ) (A : Tensor0SSpace s I x) (slots : Fin s -> Idx) :
    component0S (I := I) basis (n • A) slots =
      n • component0S (I := I) basis A slots := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.component0S_nsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.component0S_nsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.component0S_nsmul ``Submission.DifferentialGeometry.Tensor0SBundle.component0S_nsmul

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [Fintype Idx] [DecidableEq Idx] in
theorem component0S_product_field
    (A : Tensor0SSpace s I x) (B : Tensor0SSpace q I x)
    (slots : Fin (s + q) -> Idx) :
    component0S (I := I) basis
        (Bundle.continuousMultilinearMap.productFun
          (𝕜 := 𝕜) (F := E) (E := TangentSpace I) A B) slots =
      component0S (I := I) basis A (slots ∘ Fin.castAdd q) *
        component0S (I := I) basis B (slots ∘ Fin.natAdd s) := by
  have hP := Bundle.continuousMultilinearMap.product_fun_apply
    (𝕜 := 𝕜) (F := E) (E := TangentSpace I) A B
    (fun a => basis (slots a))
  simp only [component0S_apply]
  exact hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.component0S_product_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.component0S_product_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.component0S_product_field ``Submission.DifferentialGeometry.Tensor0SBundle.component0S_product_field

end Covariant

section Mixed

variable {r s : Nat}
variable (basis : Module.Basis Idx 𝕜 (TangentSpace I x))

def componentRSField
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) : 𝕜 :=
  component0S (I := I) basis (T (basisTensor0S (I := I) basis upper)) lower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.componentRSField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.componentRSField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.componentRSField ``Submission.DifferentialGeometry.Tensor0SBundle.componentRSField

omit [DecidableEq Idx] in
@[simp]
theorem componentRSField_apply
    (T : TensorRSSpace r s I x)
    (upper : Fin r -> Idx) (lower : Fin s -> Idx) :
    componentRSField (I := I) basis T upper lower =
      (T (basisTensor0S (I := I) basis upper))
        (fun a => basis (lower a)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.componentRSField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.componentRSField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.componentRSField_apply ``Submission.DifferentialGeometry.Tensor0SBundle.componentRSField_apply

omit [DecidableEq Idx] in
theorem componentRSField_congr_slots
    (T : TensorRSSpace r s I x)
    {upper upper' : Fin r -> Idx} {lower lower' : Fin s -> Idx}
    (hu : upper = upper') (hl : lower = lower') :
    componentRSField (I := I) basis T upper lower =
      componentRSField (I := I) basis T upper' lower' := by
  rw [hu, hl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.componentRSField_congr_slots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.componentRSField_congr_slots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.componentRSField_congr_slots ``Submission.DifferentialGeometry.Tensor0SBundle.componentRSField_congr_slots

omit [DecidableEq Idx] in
theorem componentRSField_apply_input_eq_sum
    (T : TensorRSSpace r s I x) (input : Tensor0SSpace r I x)
    (lower : Fin s -> Idx) :
    component0S (I := I) basis (T input) lower =
      ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRSField (I := I) basis T upper lower := by
  have hinput :
      (∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper • basisTensor0S (I := I) basis upper) =
        input := by
    simpa [basisTensor0S] using (tensor0SBasis (I := I) basis r).sum_repr input
  calc
    component0S (I := I) basis (T input) lower =
        component0S (I := I) basis
          (T (∑ upper : Fin r -> Idx,
            component0S (I := I) basis input upper •
              basisTensor0S (I := I) basis upper)) lower := by
          rw [hinput]
    _ = ∑ upper : Fin r -> Idx,
        component0S (I := I) basis input upper *
          componentRSField (I := I) basis T upper lower := by
          let inputSum : Tensor0SSpace r I x :=
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper •
                basisTensor0S (I := I) basis upper
          change component0S (I := I) basis (T inputSum) lower =
            ∑ upper : Fin r -> Idx,
              component0S (I := I) basis input upper *
                componentRSField (I := I) basis T upper lower
          rw [← congrFun (coordMap0S_apply (I := I) basis (T inputSum)) lower]
          dsimp [inputSum]
          rw [map_sum]
          simp [map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.componentRSField_apply_input_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.componentRSField_apply_input_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.componentRSField_apply_input_eq_sum ``Submission.DifferentialGeometry.Tensor0SBundle.componentRSField_apply_input_eq_sum

omit [DecidableEq Idx] in
theorem extRS_basis_field
    {A B : TensorRSSpace r s I x}
    (h : ∀ upper : Fin r -> Idx, ∀ lower : Fin s -> Idx,
      componentRSField (I := I) basis A upper lower =
        componentRSField (I := I) basis B upper lower) :
    A = B := by
  classical
  apply ContinuousLinearMap.ext
  intro input
  apply ext0S_basis (I := I) basis
  intro lower
  calc
    component0S (I := I) basis (A input) lower =
        ∑ upper : Fin r -> Idx,
          component0S (I := I) basis input upper *
            componentRSField (I := I) basis A upper lower :=
      componentRSField_apply_input_eq_sum (I := I) basis A input lower
    _ = ∑ upper : Fin r -> Idx,
          component0S (I := I) basis input upper *
            componentRSField (I := I) basis B upper lower := by
      refine Finset.sum_congr rfl fun upper _ => ?_
      rw [h upper lower]
    _ = component0S (I := I) basis (B input) lower :=
      (componentRSField_apply_input_eq_sum (I := I) basis B input lower).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.extRS_basis_field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.extRS_basis_field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.extRS_basis_field ``Submission.DifferentialGeometry.Tensor0SBundle.extRS_basis_field

end Mixed

end Tensor0SBundle
end DifferentialGeometry
