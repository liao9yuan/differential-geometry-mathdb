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
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry
namespace Tensor0SBundle

noncomputable section

open scoped _root_.Manifold _root_.ContDiff

namespace MetricFiberData

variable {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]

omit [FiniteDimensional ℝ V] in
private theorem dual_finrank_eq :
    Module.finrank Real V = Module.finrank Real (Module.Dual Real V) :=
  Subspace.dual_finrank_eq.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor0SBundle.MetricFiberData.dual_finrank_eq target :: scope.openDecls } }

variable {W : Type*} [AddCommGroup W] [Module Real W] [FiniteDimensional Real W]

end MetricFiberData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev SmoothMetricGen
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.SmoothMetricGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.SmoothMetricGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.SmoothMetricGen ``Submission.DifferentialGeometry.Tensor0SBundle.SmoothMetricGen

def tangentFlatLinearGen (g : SmoothMetricGen I M) (x : M) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    simp
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tangentFlatLinearGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tangentFlatLinearGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tangentFlatLinearGen ``Submission.DifferentialGeometry.Tensor0SBundle.tangentFlatLinearGen

omit [FiniteDimensional ℝ E] in
@[simp] theorem tangentFlatLinear_apply_gen
    (g : SmoothMetricGen I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatLinearGen (I := I) g x v w = g.inner x v w := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_apply_gen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_apply_gen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_apply_gen ``Submission.DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_apply_gen

omit [FiniteDimensional ℝ E] in
theorem tangentFlatLinear_injective_gen
    (g : SmoothMetricGen I M) (x : M) :
    Function.Injective (tangentFlatLinearGen (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [tangentFlatLinear_apply_gen] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective_gen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective_gen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective_gen ``Submission.DifferentialGeometry.Tensor0SBundle.tangentFlatLinear_injective_gen

def tangentFlatEquivGen (g : SmoothMetricGen I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (tangentFlatLinearGen (I := I) g x)
    (tangentFlatLinear_injective_gen (I := I) g x)
    MetricFiberData.dual_finrank_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tangentFlatEquivGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tangentFlatEquivGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tangentFlatEquivGen ``Submission.DifferentialGeometry.Tensor0SBundle.tangentFlatEquivGen

@[simp] theorem tangentFlatEquiv_apply_gen
    (g : SmoothMetricGen I M) (x : M)
    (v w : TangentSpace I x) :
    tangentFlatEquivGen (I := I) g x v w = g.inner x v w := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tangentFlatEquiv_apply_gen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tangentFlatEquiv_apply_gen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tangentFlatEquiv_apply_gen ``Submission.DifferentialGeometry.Tensor0SBundle.tangentFlatEquiv_apply_gen

structure TangentMetricDataGen
    (g : SmoothMetricGen I M) (x : M) where
  metric : MetricFiberData (TangentSpace I x)
  realizes_inner : forall X Y : TangentSpace I x,
    metric.inner X Y = g.inner x X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen ``Submission.DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen

def tangentMetricDataGen (g : SmoothMetricGen I M) (x : M) :
    TangentMetricDataGen (I := I) g x where
  metric :=
    { flat := tangentFlatEquivGen (I := I) g x
      symm := by
        intro X Y
        exact g.symm x X Y
      nonneg := by
        intro X
        by_cases hX : X = 0
        · simp [hX]
        · exact le_of_lt (g.pos x X hX) }
  realizes_inner := by
    intro X Y
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.tangentMetricDataGen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.tangentMetricDataGen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.tangentMetricDataGen ``Submission.DifferentialGeometry.Tensor0SBundle.tangentMetricDataGen

namespace TangentMetricDataGen

theorem inner_eq_gen
    {g : SmoothMetricGen I M} {x : M} (D : TangentMetricDataGen (I := I) g x)
    (X Y : TangentSpace I x) :
    D.metric.inner X Y = g.inner x X Y :=
  D.realizes_inner X Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen.inner_eq_gen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen.inner_eq_gen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen.inner_eq_gen ``Submission.DifferentialGeometry.Tensor0SBundle.TangentMetricDataGen.inner_eq_gen

end TangentMetricDataGen

end

end Tensor0SBundle
end DifferentialGeometry
