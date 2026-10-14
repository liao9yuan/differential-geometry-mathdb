import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis
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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Fiber
import Submission.DifferentialGeometry.Tensor.Multilinear.Curry.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Submission.DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

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

section ModelBasis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

end ModelBasis

section Tensor0S

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {s : Nat} {x : M}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tensor0S_sum_apply {ι : Type*} [Fintype ι]
    (T : ι -> Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    ((∑ i : ι, T i) v) = ∑ i : ι, (T i) v := by
  classical
  let S : Finset ι := Finset.univ
  change ((∑ i ∈ S, T i) v) = ∑ i ∈ S, (T i) v
  induction S using Finset.induction_on with
  | empty =>
      exact Tensor0SSpace.zero_apply s x v
  | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change T a v + (∑ i ∈ S, T i) v = T a v + ∑ i ∈ S, T i v
      rw [ih]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensor0S_sum_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensor0S_sum_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensor0S_sum_apply ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0S_sum_apply

omit [DecidableEq Idx] in
theorem basisTensor0S_apply
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (slots : Fin s -> Idx) (v : Fin s -> TangentSpace I x) :
    basisTensor0S (I := I) basis slots v =
      ∏ a : Fin s, basis.coord (slots a) (v a) := by
  classical
  change (continuousMultilinearMapBasis basis s slots) v =
    ∏ a : Fin s, basis.coord (slots a) (v a)
  rw [continuousMultilinearMapBasis_apply]
  simp [continuousMultilinearMapBasisElem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.basisTensor0S_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.basisTensor0S_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.basisTensor0S_apply ``Submission.DifferentialGeometry.Tensor0SBundle.basisTensor0S_apply

omit [DecidableEq Idx] in
theorem tensor0S_apply_eq_sum
    (basis : Module.Basis Idx 𝕜 (TangentSpace I x))
    (A : Tensor0SSpace s I x) (v : Fin s -> TangentSpace I x) :
    A v =
      ∑ slots : Fin s -> Idx,
        component0S (I := I) basis A slots *
          ∏ a : Fin s, basis.coord (slots a) (v a) := by
  classical
  conv_lhs => rw [← (tensor0SBasis (I := I) basis s).sum_repr A]
  rw [tensor0S_sum_apply]
  refine Finset.sum_congr rfl ?_
  intro slots _hslots
  rw [tensor0SBasis_repr]
  change component0S (I := I) basis A slots *
      ((tensor0SBasis (I := I) basis s) slots) v =
    component0S (I := I) basis A slots *
      ∏ a : Fin s, basis.coord (slots a) (v a)
  have hb :
      ((tensor0SBasis (I := I) basis s) slots) v =
        ∏ a : Fin s, basis.coord (slots a) (v a) := by
    change basisTensor0S (I := I) basis slots v =
      ∏ a : Fin s, basis.coord (slots a) (v a)
    exact basisTensor0S_apply (I := I) basis slots v
  rw [hb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tensor0S_apply_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tensor0S_apply_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tensor0S_apply_eq_sum ``Submission.DifferentialGeometry.Tensor0SBundle.tensor0S_apply_eq_sum

end Tensor0S

end Tensor0SBundle
end DifferentialGeometry
