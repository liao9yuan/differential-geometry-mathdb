import Submission.DifferentialGeometry.Geometry.Curvature.Riemann.RawFields
import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Tensor
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import Submission.DifferentialGeometry.Tensor.RSTensor.Algebra.Contraction
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
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.TensorProduct
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
import Submission.DifferentialGeometry.Tensor.RSTensor.Field
import Submission.DifferentialGeometry.Tensor.Multilinear.PredualBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Trace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev Tensor13Section :=
  TensorRSField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 1 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor13Section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor13Section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor13Section ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor13Section


abbrev Tensor04Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor04Section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor04Section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor04Section ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor04Section


abbrev FourTensorField := Tensor04Section (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.FourTensorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.FourTensorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.FourTensorField ``Submission.DifferentialGeometry.Geometry.Curvature.FourTensorField


abbrev Tensor02Section :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) ∞ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor02Section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor02Section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor02Section ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor02Section


abbrev TwoTensorField := Tensor02Section (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.TwoTensorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.TwoTensorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.TwoTensorField ``Submission.DifferentialGeometry.Geometry.Curvature.TwoTensorField


abbrev Tensor02At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor02At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor02At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor02At ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor02At


abbrev Tensor04At (x : M) :=
  Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor04At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor04At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor04At ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor04At


abbrev Tensor13At (x : M) :=
  TensorRSSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 3 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.Tensor13At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.Tensor13At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.Tensor13At ``Submission.DifferentialGeometry.Geometry.Curvature.Tensor13At

def scalarOne0S (x : M) : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 0 x :=
  ContinuousMultilinearMap.constOfIsEmpty Real
    (fun _ : Fin 0 => TangentSpace I x) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.scalarOne0S then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.scalarOne0S"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.scalarOne0S ``Submission.DifferentialGeometry.Geometry.Curvature.scalarOne0S

def ricciFromRm13At {x : M} (Rm13 : Tensor13At (I := I) (M := M) x) :
    Tensor02At (I := I) (M := M) x :=
  (contractTrace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 0 2 x Rm13)
    (scalarOne0S (I := I) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciFromRm13At then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciFromRm13At"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciFromRm13At ``Submission.DifferentialGeometry.Geometry.Curvature.ricciFromRm13At


def vec2 {x : M} (X Y : TangentSpace I x) : Fin 2 -> TangentSpace I x :=
  fun i => if i = 0 then X else Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.vec2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.vec2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.vec2 ``Submission.DifferentialGeometry.Geometry.Curvature.vec2


def vec3 {x : M} (X Y Z : TangentSpace I x) : Fin 3 -> TangentSpace I x :=
  fun i => if i = 0 then X else if i = 1 then Y else Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.vec3 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.vec3"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.vec3 ``Submission.DifferentialGeometry.Geometry.Curvature.vec3


def vec4 {x : M} (W X Y Z : TangentSpace I x) : Fin 4 -> TangentSpace I x :=
  fun i => if i = 0 then W else if i = 1 then X else if i = 2 then Y else Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.vec4 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.vec4"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.vec4 ``Submission.DifferentialGeometry.Geometry.Curvature.vec4


def tensor02ToField (Ric : Tensor02Section (I := I) (M := M)) :
    RawTwoTensorField (I := I) (M := M) :=
  fun x X Y => Ric x (vec2 X Y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor02ToField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor02ToField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor02ToField ``Submission.DifferentialGeometry.Geometry.Curvature.tensor02ToField


def tensor04ToField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  fun x X Y Z W => Rm04 x (vec4 X Y Z W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04ToField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04ToField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04ToField ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04ToField

def tensor04StandardAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) : Real :=
  Rm04 (vec4 X Y Z W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt

def tensor04OutAt {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) : Real :=
  Rm04 (vec4 X Y Z W)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04OutAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04OutAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04OutAt ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04OutAt

def tensor04StandardToOutPerm : Equiv.Perm (Fin 4) where
  toFun i := if i = 0 then 3 else if i = 1 then 0 else if i = 2 then 1 else 2
  invFun i := if i = 0 then 1 else if i = 1 then 2 else if i = 2 then 3 else 0
  left_inv i := by
    fin_cases i <;> simp
  right_inv i := by
    fin_cases i <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardToOutPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardToOutPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardToOutPerm ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardToOutPerm

def tensor04StandardOfOutAt {x : M} (Rm04Out : Tensor04At (I := I) (M := M) x) :
    Tensor04At (I := I) (M := M) x :=
  Rm04Out.domDomCongr tensor04StandardToOutPerm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt

omit [FiniteDimensional ℝ E] in
@[simp]
theorem tensor04StandardAt_apply
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StandardAt (I := I) (M := M) Rm04 X Y Z W =
      Rm04 (vec4 X Y Z W) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardAt_apply

omit [FiniteDimensional ℝ E] in
@[simp]
theorem tensor04OutAt_apply
    {x : M} (Rm04 : Tensor04At (I := I) (M := M) x)
    (W X Y Z : TangentSpace I x) :
    tensor04OutAt (I := I) (M := M) Rm04 W X Y Z =
      Rm04 (vec4 X Y Z W) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04OutAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04OutAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04OutAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04OutAt_apply

omit [FiniteDimensional ℝ E] in
@[simp]
theorem tensor04StandardOfOutAt_apply
    {x : M} (Rm04Out : Tensor04At (I := I) (M := M) x)
    (X Y Z W : TangentSpace I x) :
    tensor04StandardOfOutAt (I := I) (M := M) Rm04Out (vec4 X Y Z W) =
      Rm04Out (vec4 W X Y Z) := by
  change Rm04Out (fun i => (vec4 X Y Z W) (tensor04StandardToOutPerm i)) =
    Rm04Out (vec4 W X Y Z)
  congr 1
  funext i
  fin_cases i <;> simp [tensor04StandardToOutPerm, vec4]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt_apply ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04StandardOfOutAt_apply

def tensor04ToStandardField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  fun x X Y Z W => tensor04StandardAt (I := I) (Rm04 x) X Y Z W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04ToStandardField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04ToStandardField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04ToStandardField ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04ToStandardField

def tensor04ToOutField (Rm04 : Tensor04Section (I := I) (M := M)) :
    RawFourTensorField (I := I) (M := M) :=
  fun x W X Y Z => tensor04OutAt (I := I) (Rm04 x) W X Y Z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.tensor04ToOutField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.tensor04ToOutField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.tensor04ToOutField ``Submission.DifferentialGeometry.Geometry.Curvature.tensor04ToOutField


def ricciComp
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j : Idx) : Real :=
  Ric x (vec2 (frame i x) (frame j x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciComp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciComp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciComp ``Submission.DifferentialGeometry.Geometry.Curvature.ricciComp


def rm04Comp
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) : Real :=
  Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04Comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04Comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04Comp ``Submission.DifferentialGeometry.Geometry.Curvature.rm04Comp

def rm13Comp
    {Idx : Type*} {u : Set M}
    (Rm13 : Tensor13Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E ∞ frame u)
    (x : M) (a b c d : Idx) : Real :=
  Rm13 x (dualToCotangent (hframe.coeff a x)) (vec3 (frame b x) (frame c x) (frame d x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm13Comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm13Comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm13Comp ``Submission.DifferentialGeometry.Geometry.Curvature.rm13Comp

structure CurvatureSections where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  scalar : M -> Real
  scalarSmooth : ContMDiff I 𝓘(Real) ∞ scalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.CurvatureSections then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.CurvatureSections"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.CurvatureSections ``Submission.DifferentialGeometry.Geometry.Curvature.CurvatureSections

@[simp]
theorem rm04_comp_eq_eval
    {Idx : Type*}
    (Rm04 : Tensor04Section (I := I) (M := M))
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (x : M) (i j k l : Idx) :
    rm04Comp (I := I) Rm04 frame x i j k l =
      Rm04 x (vec4 (frame i x) (frame j x) (frame k x) (frame l x)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_eval ``Submission.DifferentialGeometry.Geometry.Curvature.rm04_comp_eq_eval

end DifferentialGeometry.Geometry.Curvature
