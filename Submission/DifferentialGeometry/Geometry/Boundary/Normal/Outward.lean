import Submission.DifferentialGeometry.Geometry.Boundary.Metric.Induced
import Submission.DifferentialGeometry.Geometry.Boundary.Metric.GramMatrix
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Submission.DifferentialGeometry.Tensor.BilinearForm
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Set _root_.Function _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

abbrev inwardCoordE : E := hI.inwardCoordE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordE ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordE

def inwardCoord (x : BoundaryManifold I M) : TangentSpace I (x : M) :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x : M)).symm (x : M) hI.inwardCoordE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord

omit [FiniteDimensional ℝ E] in
lemma inwardCoord_eq (x : BoundaryManifold I M) :
    tangentSpaceModelContinuousLinearEquiv (I := I) (x : M) (inwardCoord (M := M) x) =
      hI.inwardCoordE := by
  have h_symmL : inwardCoord (M := M) x =
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x : M)).symmL ℝ (x : M)) hI.inwardCoordE := by
    unfold inwardCoord
    exact (Bundle.Trivialization.symmL_apply (R := ℝ)
      (e := _root_.FiberBundle.trivializationAt E (TangentSpace I) (x : M))
      (_root_.FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (x : M)) hI.inwardCoordE).symm
  unfold tangentSpaceModelContinuousLinearEquiv
  rw [h_symmL,
      TangentBundle.symmL_trivializationAt
        (x₀ := (x : M)) (x := (x : M)) (mem_chart_source H _),
      mfderivWithin_range_extChartAt_symm]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord_eq ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoord_eq

def inwardCoordAt (α₀ : BoundaryManifold I M) (x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).symm (x : M) hI.inwardCoordE

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt

omit [FiniteDimensional ℝ E] in
@[simp] lemma inwardCoordAt_self (x : BoundaryManifold I M) :
    inwardCoordAt (M := M) x x = inwardCoord (M := M) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_self ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_self

end Model

open _root_.Submission.DifferentialGeometry.Integral.Measure

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

def normalSubspace (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    Submodule ℝ (TangentSpace I (x : M)) where
  carrier := {v : TangentSpace I (x : M) | ∀ w : TangentSpace hI.boundaryI x,
    g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) = 0}
  zero_mem' := by
    intro w
    simp
  add_mem' := by
    intro v₁ v₂ h₁ h₂ w
    rw [map_add, add_apply, h₁ w, h₂ w, add_zero]
  smul_mem' := by
    intro c v hv w
    rw [map_smul, smul_apply, hv w, smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace

omit [FiniteDimensional ℝ E] in
@[simp] lemma mem_normalSubspace_iff
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) :
    v ∈ normalSubspace (M := M) g x ↔
      ∀ w : TangentSpace hI.boundaryI x,
        g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) = 0 :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mem_normalSubspace_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mem_normalSubspace_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mem_normalSubspace_iff ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mem_normalSubspace_iff

omit [FiniteDimensional ℝ E] in
lemma inner_normalSubspace_dincl
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    {v : TangentSpace I (x : M)} (hv : v ∈ normalSubspace (M := M) g x)
    (w : TangentSpace hI.boundaryI x) :
    g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) = 0 := hv w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_normalSubspace_dincl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_normalSubspace_dincl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_normalSubspace_dincl ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_normalSubspace_dincl

omit [FiniteDimensional ℝ E] in
lemma inner_dincl_normalSubspace
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    {v : TangentSpace I (x : M)} (hv : v ∈ normalSubspace (M := M) g x)
    (w : TangentSpace hI.boundaryI x) :
    g.inner (x : M) (boundaryInclusionMfderiv (M := M) x w) v = 0 := by
  rw [g.symm (x : M) _ v]; exact hv w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_normalSubspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_normalSubspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_normalSubspace ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_normalSubspace

variable (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)

def boundaryFunOfInward : TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ where
  toFun w := g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w)
  map_add' u v := by
    rw [ContinuousLinearMap.map_add (boundaryInclusionMfderiv (M := M) x) u v]
    exact ContinuousLinearMap.map_add (g.inner (x : M) (inwardCoord (M := M) x)) _ _
  map_smul' c v := by
    rw [ContinuousLinearMap.map_smul (boundaryInclusionMfderiv (M := M) x) c v]
    exact ContinuousLinearMap.map_smul (g.inner (x : M) (inwardCoord (M := M) x)) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryFunOfInward_apply (w : TangentSpace hI.boundaryI x) :
    boundaryFunOfInward (M := M) g x w =
      g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInward_apply

private def boundaryFlatLinear :
    TangentSpace hI.boundaryI x →ₗ[ℝ] (TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ) where
  toFun u := (inducedMetricInner (M := M) g x u).toLinearMap
  map_add' u v := by
    ext w
    change inducedMetricInner (M := M) g x (u + v) w =
      inducedMetricInner (M := M) g x u w + inducedMetricInner (M := M) g x v w
    rw [map_add, add_apply]
  map_smul' c v := by
    ext w
    change inducedMetricInner (M := M) g x (c • v) w =
      c • inducedMetricInner (M := M) g x v w
    rw [map_smul, smul_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFlatLinear_apply (u v : TangentSpace hI.boundaryI x) :
    boundaryFlatLinear (M := M) g x u v = inducedMetricInner (M := M) g x u v := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatLinear_injective :
    Function.Injective (boundaryFlatLinear (M := M) g x) := by
  intro u v hpoint
  by_contra hne
  have huv_ne : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < inducedMetricInner (M := M) g x (u - v) (u - v) :=
    inducedMetricInner_pos (M := M) g x (u - v) huv_ne
  have hzero : ∀ z : TangentSpace hI.boundaryI x,
      inducedMetricInner (M := M) g x (u - v) z = 0 := by
    intro z
    have h := congrArg (fun L : TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ => L z) hpoint
    simp only [boundaryFlatLinear_apply] at h
    have hsub : inducedMetricInner (M := M) g x (u - v) z =
        inducedMetricInner (M := M) g x u z - inducedMetricInner (M := M) g x v z := by
      rw [map_sub, sub_apply]
    rw [hsub, sub_eq_zero]; exact h
  exact (lt_irrefl 0) (hzero (u - v) ▸ hpos)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear_injective target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatLinear_finrank_eq :
    Module.finrank ℝ (TangentSpace hI.boundaryI x) =
      Module.finrank ℝ (TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear_finrank_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatLinear_finrank_eq target :: scope.openDecls } }

private def boundaryFlatMap :
    TangentSpace hI.boundaryI x ≃ₗ[ℝ] (TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (boundaryFlatLinear (M := M) g x)
    (boundaryFlatLinear_injective g x)
    (boundaryFlatLinear_finrank_eq x)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatMap target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFlatMap_apply (u v : TangentSpace hI.boundaryI x) :
    boundaryFlatMap (M := M) g x u v = inducedMetricInner (M := M) g x u v := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatMap_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatMap_apply target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatMap_apply_symm
    (α : TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ) (w : TangentSpace hI.boundaryI x) :
    inducedMetricInner (M := M) g x ((boundaryFlatMap (M := M) g x).symm α) w = α w := by
  have h := (boundaryFlatMap (M := M) g x).apply_symm_apply α
  have hh : boundaryFlatMap (M := M) g x ((boundaryFlatMap (M := M) g x).symm α) w = α w :=
    congrArg (fun L : TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ => L w) h
  rw [boundaryFlatMap_apply] at hh
  exact hh

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatMap_apply_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatMap_apply_symm target :: scope.openDecls } }

def boundaryComponentOfInward : TangentSpace hI.boundaryI x :=
  (boundaryFlatMap (M := M) g x).symm (boundaryFunOfInward (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInward ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInward
omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_boundaryComponentOfInward (w : TangentSpace hI.boundaryI x) :
    inducedMetricInner (M := M) g x (boundaryComponentOfInward (M := M) g x) w =
      g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w) := by
  unfold boundaryComponentOfInward
  have := boundaryFlatMap_apply_symm (M := M) g x (boundaryFunOfInward (M := M) g x) w
  rw [this]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInward ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInward

def inwardTangentialPart : TangentSpace I (x : M) :=
  boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInward (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart
omit [FiniteDimensional ℝ E] in
@[simp] lemma inwardTangentialPart_def :
    inwardTangentialPart (M := M) g x =
      boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInward (M := M) g x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPart_def

def outwardDir : TangentSpace I (x : M) :=
  inwardTangentialPart (M := M) g x - inwardCoord (M := M) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir
omit [FiniteDimensional ℝ E] in
@[simp] lemma outwardDir_def :
    outwardDir (M := M) g x =
      inwardTangentialPart (M := M) g x - inwardCoord (M := M) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_def
omit [FiniteDimensional ℝ E] in
theorem outwardDir_mem_normalSubspace :
    outwardDir (M := M) g x ∈ normalSubspace (M := M) g x := by
  intro w
  rw [outwardDir_def]
  have hsub : g.inner (x : M)
        (inwardTangentialPart (M := M) g x - inwardCoord (M := M) x)
        (boundaryInclusionMfderiv (M := M) x w) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (boundaryInclusionMfderiv (M := M) x w) -
      g.inner (x : M) (inwardCoord (M := M) x) (boundaryInclusionMfderiv (M := M) x w) := by
    rw [map_sub, sub_apply]
  rw [hsub]
  have h1 : g.inner (x : M) (inwardTangentialPart (M := M) g x)
    (boundaryInclusionMfderiv (M := M) x w) =
      inducedMetricInner (M := M) g x (boundaryComponentOfInward (M := M) g x) w := by
    rw [inducedMetricInner_apply, inwardTangentialPart_def]
  rw [h1]
  rw [inducedMetricInner_boundaryComponentOfInward (M := M) g x w]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_mem_normalSubspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_mem_normalSubspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_mem_normalSubspace ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_mem_normalSubspace
omit [FiniteDimensional ℝ E] in
theorem det_gram_inwardCoord_boundaryChartBasis :
    (Matrix.of fun i j : Fin (Module.finrank Real hI.boundaryE + 1) =>
      g.inner (x : M)
        (Fin.cons (α := fun _ => TangentSpace I (x : M)) (inwardCoord (M := M) x)
          (fun k => boundaryInclusionMfderiv x (boundaryChartBasisVecFiber x k x)) i)
        (Fin.cons (α := fun _ => TangentSpace I (x : M)) (inwardCoord (M := M) x)
          (fun k => boundaryInclusionMfderiv x (boundaryChartBasisVecFiber x k x)) j)).det =
      g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) *
        (boundaryGramMatrix g x x).det := by
  let b := boundaryChartBasisFamily (M := M) x
    (_root_.FiberBundle.mem_baseSet_trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x)
  let c : Fin (Module.finrank Real hI.boundaryE) → Real :=
    fun i => b.repr (boundaryComponentOfInward (M := M) g x) i
  let v : Fin (Module.finrank Real hI.boundaryE) → TangentSpace I (x : M) :=
    fun i => boundaryInclusionMfderiv x (boundaryChartBasisVecFiber x i x)
  have hsum : (∑ i, c i • v i) = inwardTangentialPart (M := M) g x := by
    rw [inwardTangentialPart_def, ← b.sum_repr (boundaryComponentOfInward (M := M) g x), map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
  have hw : (∑ i, c i • v i) - inwardCoord (M := M) x = outwardDir (M := M) g x := by
    rw [hsum, outwardDir_def]
  have h := (g.inner (x : M)).toBilinForm.det_gram_cons_eq_mul_of_orthogonal
    (inwardCoord (M := M) x) v c (by
      intro i
      rw [hw]
      exact outwardDir_mem_normalSubspace g x (boundaryChartBasisVecFiber x i x))
  rw [hw] at h
  have hgram : (Matrix.of fun i j => (g.inner (x : M)).toBilinForm (v i) (v j)) =
      boundaryGramMatrix g x x := by
    ext i j
    exact (inducedMetricInner_apply g x (boundaryChartBasisVecFiber x i x)
      (boundaryChartBasisVecFiber x j x)).symm
  rw [hgram] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.det_gram_inwardCoord_boundaryChartBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.det_gram_inwardCoord_boundaryChartBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.det_gram_inwardCoord_boundaryChartBasis ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.det_gram_inwardCoord_boundaryChartBasis

omit [FiniteDimensional ℝ E] in
lemma g_inner_outwardDir_inwardCoord :
    g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) := by
  rw [outwardDir_def, map_sub, sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord
omit [FiniteDimensional ℝ E] in
lemma g_inner_inwardCoord_outwardDir :
    g.inner (x : M) (inwardCoord (M := M) x) (outwardDir (M := M) g x) =
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) := by
  rw [g.symm (x : M) (inwardCoord (M := M) x) (outwardDir (M := M) g x)]
  exact g_inner_outwardDir_inwardCoord (M := M) g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_inwardCoord_outwardDir then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_inwardCoord_outwardDir"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_inwardCoord_outwardDir ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_inwardCoord_outwardDir
omit [FiniteDimensional ℝ E] in
lemma g_inner_outwardDir_outwardDir :
    g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) =
      g.inner (x : M) (inwardCoord (M := M) x) (inwardCoord (M := M) x) -
      g.inner (x : M) (inwardTangentialPart (M := M) g x) (inwardCoord (M := M) x) := by
  have h_orth : g.inner (x : M) (outwardDir (M := M) g x)
      (inwardTangentialPart (M := M) g x) = 0 := by
    have hmem : outwardDir (M := M) g x ∈ normalSubspace (M := M) g x :=
      outwardDir_mem_normalSubspace (M := M) g x
    rw [inwardTangentialPart_def]
    exact hmem (boundaryComponentOfInward (M := M) g x)
  have hdecomp : g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) =
      g.inner (x : M) (outwardDir (M := M) g x) (inwardTangentialPart (M := M) g x) -
      g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) := by
    change g.inner (x : M) (outwardDir (M := M) g x)
        (inwardTangentialPart (M := M) g x - inwardCoord (M := M) x) =
      g.inner (x : M) (outwardDir (M := M) g x) (inwardTangentialPart (M := M) g x) -
      g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x)
    exact ContinuousLinearMap.map_sub _ _ _
  rw [hdecomp, h_orth, zero_sub]
  rw [g_inner_outwardDir_inwardCoord (M := M) g x]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_outwardDir then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_outwardDir"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_outwardDir ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_outwardDir

def InwardCoordTransverse (x : BoundaryManifold I M) : Prop :=
  inwardCoord (M := M) x ∉ LinearMap.range (boundaryInclusionMfderiv (M := M) x).toLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse
omit [FiniteDimensional ℝ E] in
theorem InwardCoordTransverse_of_HasSmoothBoundary
    (x : BoundaryManifold I M) :
    InwardCoordTransverse (M := M) x := by
  by_cases hN : Nonempty hI.boundaryH
  · have := hN
    intro hmem
    rcases hmem with ⟨w, hw⟩
    apply hI.inwardCoordE_transverse (extChartAt hI.boundaryI x x)
    change hI.inwardCoordE ∈ Set.range
      (fderiv ℝ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm)
        (extChartAt hI.boundaryI x x))
    rw [← boundaryInclusionMfderiv_model_eq_fderiv (I := I) (M := M) x]
    refine ⟨tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x w, ?_⟩
    change tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)
        (boundaryInclusionMfderiv (M := M) x
          ((tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm
            (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x w))) =
      hI.inwardCoordE
    rw [(tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) x).symm_apply_apply]
    exact (congrArg (tangentSpaceModelContinuousLinearEquiv (I := I) (x : M)) hw).trans
      (inwardCoord_eq (M := M) x)
  · have : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    have : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false x).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse_of_HasSmoothBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse_of_HasSmoothBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse_of_HasSmoothBoundary ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.InwardCoordTransverse_of_HasSmoothBoundary
omit [FiniteDimensional ℝ E] in
theorem outwardDir_ne_zero :
    outwardDir (M := M) g x ≠ 0 := by
  intro h0
  have htr : InwardCoordTransverse (M := M) x :=
    InwardCoordTransverse_of_HasSmoothBoundary (M := M) x
  have h_eq : inwardCoord (M := M) x = inwardTangentialPart (M := M) g x := by
    have := h0
    rw [outwardDir_def, sub_eq_zero] at this
    exact this.symm
  apply htr
  rw [h_eq, inwardTangentialPart_def]
  exact ⟨boundaryComponentOfInward (M := M) g x, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_ne_zero ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDir_ne_zero
omit [FiniteDimensional ℝ E] in
theorem g_inner_outwardDir_pos :
    0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
  g.pos (x : M) _ (outwardDir_ne_zero (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_pos ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_pos
omit [FiniteDimensional ℝ E] in
theorem g_inner_outwardDir_inwardCoord_neg :
    g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) < 0 := by
  have hpos : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
    g_inner_outwardDir_pos (M := M) g x
  have h_id : g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      -g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) := by
    rw [g_inner_outwardDir_inwardCoord (M := M) g x,
        g_inner_outwardDir_outwardDir (M := M) g x]
    ring
  rw [h_id]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord_neg ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDir_inwardCoord_neg

def outwardNormal : TangentSpace I (x : M) :=
  open scoped _root_.Classical in
  if _h : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) then
    (Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)))⁻¹ •
      outwardDir (M := M) g x
  else
    0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal
omit [FiniteDimensional ℝ E] in
lemma outwardNormal_eq :
    outwardNormal (M := M) g x =
      (Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x)))⁻¹ • outwardDir (M := M) g x := by
  unfold outwardNormal
  rw [dif_pos (g_inner_outwardDir_pos (M := M) g x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_eq ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_eq
omit [FiniteDimensional ℝ E] in
theorem outwardNormal_mem_normalSubspace :
    outwardNormal (M := M) g x ∈ normalSubspace (M := M) g x := by
  rw [outwardNormal_eq (M := M) g x]
  exact (normalSubspace (M := M) g x).smul_mem _
    (outwardDir_mem_normalSubspace (M := M) g x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_mem_normalSubspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_mem_normalSubspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_mem_normalSubspace ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_mem_normalSubspace
omit [FiniteDimensional ℝ E] in
theorem outwardNormal_orthogonal_to_boundary (w : TangentSpace hI.boundaryI x) :
    g.inner (x : M) (outwardNormal (M := M) g x) (boundaryInclusionMfderiv (M := M) x w) = 0 :=
  (outwardNormal_mem_normalSubspace (M := M) g x) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_orthogonal_to_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_orthogonal_to_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_orthogonal_to_boundary ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_orthogonal_to_boundary
omit [FiniteDimensional ℝ E] in
theorem inner_dincl_outwardNormal (w : TangentSpace hI.boundaryI x) :
    g.inner (x : M) (boundaryInclusionMfderiv (M := M) x w) (outwardNormal (M := M) g x) = 0 := by
  rw [g.symm (x : M) _ (outwardNormal (M := M) g x)]
  exact outwardNormal_orthogonal_to_boundary (M := M) g x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_outwardNormal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_outwardNormal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_outwardNormal ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inner_dincl_outwardNormal
omit [FiniteDimensional ℝ E] in
theorem outwardNormal_norm_one :
    g.inner (x : M) (outwardNormal (M := M) g x) (outwardNormal (M := M) g x) = 1 := by
  set q : ℝ := g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) with hq_def
  have hq_pos : 0 < q := g_inner_outwardDir_pos (M := M) g x
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : Real.sqrt q ≠ 0 := ne_of_gt hsq_pos
  have hsq_sq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq_pos.le
  rw [outwardNormal_eq (M := M) g x]
  have h1 : g.inner (x : M) ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x)
          ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
      (Real.sqrt q)⁻¹ • (g.inner (x : M) (outwardDir (M := M) g x))
          ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) := by
    rw [show g.inner (x : M) ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
        (Real.sqrt q)⁻¹ • g.inner (x : M) (outwardDir (M := M) g x) from
          map_smul _ _ _]
    rfl
  rw [h1]
  rw [show (g.inner (x : M) (outwardDir (M := M) g x))
        ((Real.sqrt q)⁻¹ • outwardDir (M := M) g x) =
      (Real.sqrt q)⁻¹ • g.inner (x : M) (outwardDir (M := M) g x)
        (outwardDir (M := M) g x) from
    ContinuousLinearMap.map_smul _ _ _]
  rw [show g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) = q from rfl]
  rw [smul_eq_mul, smul_eq_mul]
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = q / (Real.sqrt q * Real.sqrt q) by
    field_simp]
  rw [hsq_sq]
  exact div_self hq_ne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_norm_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_norm_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_norm_one ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_norm_one
omit [FiniteDimensional ℝ E] in
theorem outwardNormal_inner_inwardCoord_eq_neg_sqrt :
    g.inner (x : M) (outwardNormal (M := M) g x) (inwardCoord (M := M) x) =
      -Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)) := by
  have hq : 0 < g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) :=
    g_inner_outwardDir_pos g x
  have hin : g.inner (x : M) (outwardDir (M := M) g x) (inwardCoord (M := M) x) =
      -g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x) := by
    rw [g_inner_outwardDir_inwardCoord, g_inner_outwardDir_outwardDir]
    ring
  rw [outwardNormal_eq, map_smul, smul_apply, smul_eq_mul, hin, mul_neg]
  congr 1
  exact (inv_mul_eq_iff_eq_mul₀ (ne_of_gt (Real.sqrt_pos.mpr hq))).mpr
    (Real.mul_self_sqrt hq.le).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_eq_neg_sqrt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_eq_neg_sqrt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_eq_neg_sqrt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_eq_neg_sqrt


omit [FiniteDimensional ℝ E] in
theorem outwardNormal_inner_inwardCoord_neg :
    g.inner (x : M) (outwardNormal (M := M) g x) (inwardCoord (M := M) x) < 0 := by
  rw [outwardNormal_inner_inwardCoord_eq_neg_sqrt]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr (g_inner_outwardDir_pos g x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_neg ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_inwardCoord_neg

def boundaryFunOfInwardAt (g : SmoothRiemannianMetric I M)
    (α₀ x : BoundaryManifold I M) : TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ where
  toFun w := g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w)
  map_add' u v := by
    rw [ContinuousLinearMap.map_add (boundaryInclusionMfderiv (M := M) x) u v]
    exact ContinuousLinearMap.map_add
      (g.inner (x : M) (inwardCoordAt (M := M) α₀ x)) _ _
  map_smul' c v := by
    rw [ContinuousLinearMap.map_smul (boundaryInclusionMfderiv (M := M) x) c v]
    exact ContinuousLinearMap.map_smul
      (g.inner (x : M) (inwardCoordAt (M := M) α₀ x)) _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryFunOfInwardAt_apply
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M)
    (w : TangentSpace hI.boundaryI x) :
    boundaryFunOfInwardAt (M := M) g α₀ x w =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_apply

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryFunOfInwardAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    boundaryFunOfInwardAt (M := M) g x x = boundaryFunOfInward (M := M) g x := by
  ext w
  simp [boundaryFunOfInwardAt_apply, boundaryFunOfInward_apply,
    inwardCoordAt_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_self ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAt_self

def boundaryComponentOfInwardAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace hI.boundaryI x :=
  (boundaryFlatMap (M := M) g x).symm (boundaryFunOfInwardAt (M := M) g α₀ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt
omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryComponentOfInwardAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    boundaryComponentOfInwardAt (M := M) g x x =
      boundaryComponentOfInward (M := M) g x := by
  unfold boundaryComponentOfInwardAt boundaryComponentOfInward
  rw [boundaryFunOfInwardAt_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt_self ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAt_self
omit [FiniteDimensional ℝ E] in
lemma inducedMetricInner_boundaryComponentOfInwardAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M)
    (w : TangentSpace hI.boundaryI x) :
    inducedMetricInner (M := M) g x (boundaryComponentOfInwardAt (M := M) g α₀ x) w =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w) := by
  unfold boundaryComponentOfInwardAt
  have := boundaryFlatMap_apply_symm (M := M) g x
    (boundaryFunOfInwardAt (M := M) g α₀ x) w
  rw [this]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInwardAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInwardAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInwardAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_boundaryComponentOfInwardAt

def inwardTangentialPartAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInwardAt (M := M) g α₀ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt
omit [FiniteDimensional ℝ E] in
@[simp] lemma inwardTangentialPartAt_def
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    inwardTangentialPartAt (M := M) g α₀ x =
      boundaryInclusionMfderiv (M := M) x (boundaryComponentOfInwardAt (M := M) g α₀ x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_def
omit [FiniteDimensional ℝ E] in
lemma inwardTangentialPartAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    inwardTangentialPartAt (M := M) g x x = inwardTangentialPart (M := M) g x := by
  unfold inwardTangentialPartAt inwardTangentialPart
  rw [boundaryComponentOfInwardAt_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_self ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAt_self

def outwardDirAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt
omit [FiniteDimensional ℝ E] in
@[simp] lemma outwardDirAt_def
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    outwardDirAt (M := M) g α₀ x =
      inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_def ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_def
omit [FiniteDimensional ℝ E] in
lemma outwardDirAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    outwardDirAt (M := M) g x x = outwardDir (M := M) g x := by
  unfold outwardDirAt outwardDir
  rw [inwardTangentialPartAt_self, inwardCoordAt_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_self ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_self
omit [FiniteDimensional ℝ E] in
theorem outwardDirAt_mem_normalSubspace
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    outwardDirAt (M := M) g α₀ x ∈ normalSubspace (M := M) g x := by
  intro w
  rw [outwardDirAt_def]
  have hsub : g.inner (x : M)
        (inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x)
        (boundaryInclusionMfderiv (M := M) x w) =
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (boundaryInclusionMfderiv (M := M) x w) -
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (boundaryInclusionMfderiv (M := M) x w) := by
    rw [map_sub, sub_apply]
  rw [hsub]
  have h1 : g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
    (boundaryInclusionMfderiv (M := M) x w) =
      inducedMetricInner (M := M) g x (boundaryComponentOfInwardAt (M := M) g α₀ x) w := by
    rw [inducedMetricInner_apply, inwardTangentialPartAt_def]
  rw [h1]
  rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α₀ x w]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_mem_normalSubspace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_mem_normalSubspace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_mem_normalSubspace ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_mem_normalSubspace
omit [FiniteDimensional ℝ E] in
lemma g_inner_outwardDirAt_inwardCoordAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (inwardCoordAt (M := M) α₀ x) =
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) -
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (inwardCoordAt (M := M) α₀ x) := by
  rw [outwardDirAt_def, map_sub, sub_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_inwardCoordAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_inwardCoordAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_inwardCoordAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_inwardCoordAt
omit [FiniteDimensional ℝ E] in
lemma g_inner_outwardDirAt_outwardDirAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (outwardDirAt (M := M) g α₀ x) =
      g.inner (x : M) (inwardCoordAt (M := M) α₀ x) (inwardCoordAt (M := M) α₀ x) -
      g.inner (x : M) (inwardTangentialPartAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) := by
  have h_orth : g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
      (inwardTangentialPartAt (M := M) g α₀ x) = 0 := by
    have hmem : outwardDirAt (M := M) g α₀ x ∈ normalSubspace (M := M) g x :=
      outwardDirAt_mem_normalSubspace (M := M) g α₀ x
    rw [inwardTangentialPartAt_def]
    exact hmem (boundaryComponentOfInwardAt (M := M) g α₀ x)
  have hdecomp : g.inner (x : M)
        (outwardDirAt (M := M) g α₀ x) (outwardDirAt (M := M) g α₀ x) =
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x) -
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardCoordAt (M := M) α₀ x) := by
    change g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x - inwardCoordAt (M := M) α₀ x) =
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (inwardTangentialPartAt (M := M) g α₀ x) -
      g.inner (x : M) (outwardDirAt (M := M) g α₀ x) (inwardCoordAt (M := M) α₀ x)
    exact ContinuousLinearMap.map_sub _ _ _
  rw [hdecomp, h_orth, zero_sub]
  rw [g_inner_outwardDirAt_inwardCoordAt (M := M) g α₀ x]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_outwardDirAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_outwardDirAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_outwardDirAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_outwardDirAt

def outwardNormalAt
    (g : SmoothRiemannianMetric I M) (α₀ x : BoundaryManifold I M) :
    TangentSpace I (x : M) :=
  open scoped _root_.Classical in
  if _h :
    0 < g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (outwardDirAt (M := M) g α₀ x) then
    (Real.sqrt (g.inner (x : M) (outwardDirAt (M := M) g α₀ x)
        (outwardDirAt (M := M) g α₀ x)))⁻¹ • outwardDirAt (M := M) g α₀ x
  else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt
omit [FiniteDimensional ℝ E] in
@[simp] lemma outwardNormalAt_self
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    outwardNormalAt (M := M) g x x = outwardNormal (M := M) g x := by
  unfold outwardNormalAt outwardNormal
  rw [outwardDirAt_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_self ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_self

omit [FiniteDimensional ℝ E] in
theorem outwardNormalAt_inner_eq_neg_sqrt_mul_of_sub_mem_range
    (g : SmoothRiemannianMetric I M) (alpha x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) (c : Real)
    (hv : v - c • inwardCoordAt (M := M) alpha x ∈
      LinearMap.range (boundaryInclusionMfderiv (M := M) x).toLinearMap) :
    g.inner (x : M) (outwardNormalAt (M := M) g alpha x) v =
      -Real.sqrt (g.inner (x : M) (outwardDirAt (M := M) g alpha x)
        (outwardDirAt (M := M) g alpha x)) * c := by
  let q := g.inner (x : M) (outwardDirAt (M := M) g alpha x)
    (outwardDirAt (M := M) g alpha x)
  have hnormal : g.inner (x : M) (outwardDirAt (M := M) g alpha x)
      (inwardCoordAt (M := M) alpha x) = -q := by
    change g.inner (x : M) (outwardDirAt (M := M) g alpha x)
      (inwardCoordAt (M := M) alpha x) = -g.inner (x : M) (outwardDirAt (M := M) g alpha x)
        (outwardDirAt (M := M) g alpha x)
    rw [g_inner_outwardDirAt_inwardCoordAt, g_inner_outwardDirAt_outwardDirAt]
    ring
  obtain ⟨w, hw⟩ := hv
  change boundaryInclusionMfderiv x w = v - c • inwardCoordAt alpha x at hw
  have hzero := outwardDirAt_mem_normalSubspace g alpha x w
  rw [hw, map_sub, map_smul, smul_eq_mul, hnormal] at hzero
  have hinner : g.inner (x : M) (outwardDirAt (M := M) g alpha x) v = -q * c := by
    linarith
  by_cases hq : 0 < q
  · have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    change g.inner (x : M) (outwardNormalAt g alpha x) v = -Real.sqrt q * c
    rw [outwardNormalAt, dif_pos hq, map_smul, smul_apply, smul_eq_mul, hinner]
    change (Real.sqrt q)⁻¹ * (-q * c) = -Real.sqrt q * c
    field_simp
    rw [Real.sq_sqrt hq.le]
  · have hs : Real.sqrt q = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hq)
    change g.inner (x : M) (outwardNormalAt g alpha x) v = -Real.sqrt q * c
    rw [outwardNormalAt, dif_neg hq, map_zero, zero_apply, hs, neg_zero, _root_.MulZeroClass.zero_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_inner_eq_neg_sqrt_mul_of_sub_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_inner_eq_neg_sqrt_mul_of_sub_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_inner_eq_neg_sqrt_mul_of_sub_mem_range ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_inner_eq_neg_sqrt_mul_of_sub_mem_range

omit [FiniteDimensional ℝ E] in
theorem outwardNormal_inner_eq_neg_sqrt_mul_of_sub_mem_range
    (v : TangentSpace I (x : M)) (c : ℝ)
    (hv : v - c • inwardCoord (M := M) x ∈
      LinearMap.range (boundaryInclusionMfderiv (M := M) x).toLinearMap) :
    g.inner (x : M) (outwardNormal (M := M) g x) v =
      -Real.sqrt (g.inner (x : M) (outwardDir (M := M) g x) (outwardDir (M := M) g x)) * c := by
  simpa only [outwardNormalAt_self, outwardDirAt_self] using
    outwardNormalAt_inner_eq_neg_sqrt_mul_of_sub_mem_range g x x v c
      (by simpa only [inwardCoordAt_self] using hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_eq_neg_sqrt_mul_of_sub_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_eq_neg_sqrt_mul_of_sub_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_eq_neg_sqrt_mul_of_sub_mem_range ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormal_inner_eq_neg_sqrt_mul_of_sub_mem_range

end Metric

section Smoothness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]


private lemma infty_le_top_add' : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
  have h_eq : (∞ : WithTop ℕ∞) + 1 = (∞ : WithTop ℕ∞) := by
    rfl
  rw [h_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.infty_le_top_add'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.infty_le_top_add' target :: scope.openDecls } }

private noncomputable def dinclITC (x₀ : BoundaryManifold I M)
    (b : BoundaryManifold I M) (v : hI.boundaryE) : E :=
  inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
    (mfderiv hI.boundaryI I (boundaryInclusion I M)) x₀ b v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dinclITC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dinclITC target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma dinclITC_apply_contMDiffAt
    {s : BoundaryManifold I M → hI.boundaryE} {x₀ : BoundaryManifold I M}
    (hs : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞ s x₀) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M => dinclITC (M := M) x₀ b (s b)) x₀ := by
  unfold dinclITC
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) x₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_f_uncurry : ContMDiffAt (hI.boundaryI.prod hI.boundaryI) I ∞
      (Function.uncurry (fun (_ : BoundaryManifold I M) (b' : BoundaryManifold I M) =>
        boundaryInclusion I M b'))
      (x₀, x₀) := by
    have h_snd : ContMDiffAt (hI.boundaryI.prod hI.boundaryI) hI.boundaryI ∞
        (Prod.snd : BoundaryManifold I M × BoundaryManifold I M → BoundaryManifold I M)
        (x₀, x₀) := contMDiffAt_snd
    exact h_inclusion_at.comp (x₀, x₀) h_snd
  have h_g_at : ContMDiffAt hI.boundaryI hI.boundaryI ∞
      (id : BoundaryManifold I M → BoundaryManifold I M) x₀ := contMDiffAt_id
  have h_g₁_at : ContMDiffAt hI.boundaryI hI.boundaryI ∞
      (id : BoundaryManifold I M → BoundaryManifold I M) x₀ := contMDiffAt_id
  exact ContMDiffAt.mfderiv_apply
    (f := fun (_ : BoundaryManifold I M) (b : BoundaryManifold I M) => boundaryInclusion I M b)
    (g := id) (g₁ := id) (g₂ := s)
    h_f_uncurry h_g_at h_g₁_at hs infty_le_top_add'

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dinclITC_apply_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dinclITC_apply_contMDiffAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma dinclITC_apply
    (x₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (x₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH x₀).source) (v : hI.boundaryE) :
    dinclITC (M := M) x₀ b v =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ
        (b : M) (boundaryInclusionMfderiv (M := M) b
          (((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v)) := by
  unfold dinclITC
  have h_inT := inTangentCoordinates_eq_mfderiv_comp
    (I := hI.boundaryI) (I' := I) (𝕜 := ℝ)
    (f := id) (g := boundaryInclusion I M)
    (ϕ := mfderiv hI.boundaryI I (boundaryInclusion I M)) (x₀ := x₀) (x := b)
    (hx := hb_bdy) (hy := hb_amb)
  rw [h_inT]
  have h_first : mfderiv I 𝓘(ℝ, E)
      (extChartAt I (boundaryInclusion I M x₀)) (boundaryInclusion I M b)
      = (_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M) :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) hb_amb).symm
  have h_third :
      mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
        (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)
      = (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b :=
    (TangentBundle.symmL_trivializationAt hb_bdy).symm
  change ((mfderiv I 𝓘(ℝ, E) (extChartAt I (boundaryInclusion I M x₀))
          (boundaryInclusion I M b)).comp
        ((mfderiv hI.boundaryI I (boundaryInclusion I M) b).comp
          (mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI (extChartAt hI.boundaryI x₀).symm
            (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ b)))) v =
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (x₀ : M)).continuousLinearMapAt ℝ (b : M))
        ((boundaryInclusionMfderiv (M := M) b) (((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) v))
  rw [h_first, h_third]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dinclITC_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.dinclITC_apply target :: scope.openDecls } }

variable (g : SmoothRiemannianMetric I M)

private noncomputable def boundaryFlatCharted
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ :=
  ((_root_.FiberBundle.trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
    ⟨b, inducedMetricInner g b⟩).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFlatCharted (M := M) g x₀) x₀ := by
  let : NormedAddCommGroup (hI.boundaryE →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (hI.boundaryE →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  let (x : BoundaryManifold I M) : ContinuousAdd (TangentSpace hI.boundaryI x →L[ℝ] ℝ) :=
    (ContinuousLinearMap.topologicalAddGroup (𝕜₁ := ℝ) (𝕜₂ := ℝ)).toContinuousAdd
  have h_section := inducedMetricInner_contMDiff (g := g)
  have h_x₀ : x₀ ∈ (_root_.FiberBundle.trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  exact ((_root_.FiberBundle.trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
      (fun y : BoundaryManifold I M =>
        TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀).contMDiffAt_section_iff h_x₀).mp
    h_section.contMDiffAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_contMDiffAt target :: scope.openDecls } }

private noncomputable def boundaryFunOfInwardCLM
    (b : BoundaryManifold I M) : TangentSpace hI.boundaryI b →L[ℝ] ℝ :=
  (g.inner (b : M) (inwardCoord (M := M) b)).comp (boundaryInclusionMfderiv (M := M) b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCLM target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFunOfInwardCLM_apply
    (b : BoundaryManifold I M) (w : TangentSpace hI.boundaryI b) :
    boundaryFunOfInwardCLM (M := M) g b w =
      g.inner (b : M) (inwardCoord (M := M) b) (boundaryInclusionMfderiv (M := M) b w) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCLM_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCLM_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma inducedMetricInner_isInvertible
    (b : BoundaryManifold I M) :
    (inducedMetricInner (M := M) g b).IsInvertible := by
  have h_inj : Function.Injective (inducedMetricInner (M := M) g b) := by
    intro u v huv
    by_contra hne
    have huv_ne : u - v ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < inducedMetricInner (M := M) g b (u - v) (u - v) :=
      inducedMetricInner_pos (M := M) g b (u - v) huv_ne
    have hzero : inducedMetricInner (M := M) g b (u - v) (u - v) = 0 := by
      have h1 : inducedMetricInner (M := M) g b (u - v) =
          inducedMetricInner (M := M) g b u - inducedMetricInner (M := M) g b v :=
        ContinuousLinearMap.map_sub _ _ _
      rw [h1, huv, sub_self]
      simp
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  let L : TangentSpace hI.boundaryI b →ₗ[ℝ]
      (TangentSpace hI.boundaryI b →L[ℝ] ℝ) := (inducedMetricInner g b).toLinearMap
  have hL_inj : Function.Injective L := h_inj
  have hfinrank : Module.finrank ℝ (TangentSpace hI.boundaryI b) =
      Module.finrank ℝ (TangentSpace hI.boundaryI b →L[ℝ] ℝ) := by
    rw [show Module.finrank ℝ (TangentSpace hI.boundaryI b →L[ℝ] ℝ) =
        Module.finrank ℝ (TangentSpace hI.boundaryI b →ₗ[ℝ] ℝ) from ?_]
    · exact Subspace.dual_finrank_eq.symm
    · exact (LinearEquiv.finrank_eq
        (LinearMap.toContinuousLinearMap (𝕜 := ℝ)
          (E := TangentSpace hI.boundaryI b) (F' := ℝ))).symm
  let L_equiv : TangentSpace hI.boundaryI b ≃ₗ[ℝ]
      (TangentSpace hI.boundaryI b →L[ℝ] ℝ) :=
    LinearMap.linearEquivOfInjective L hL_inj hfinrank
  let L_cle : TangentSpace hI.boundaryI b ≃L[ℝ]
      (TangentSpace hI.boundaryI b →L[ℝ] ℝ) := L_equiv.toContinuousLinearEquiv
  have h_eq : (L_cle : TangentSpace hI.boundaryI b →L[ℝ]
      (TangentSpace hI.boundaryI b →L[ℝ] ℝ)) =
      inducedMetricInner (M := M) g b := by
    ext u
    rfl
  exact ⟨L_cle, h_eq⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_isInvertible
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inducedMetricInner_isInvertible target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_basepoint
    (x₀ : BoundaryManifold I M) :
    boundaryFlatCharted (M := M) g x₀ x₀ = inducedMetricInner (M := M) g x₀ := by
  refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
  have hb_bdy : x₀ ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x₀
  change ((_root_.FiberBundle.trivializationAt (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
          (fun y : BoundaryManifold I M =>
            TangentSpace hI.boundaryI y →L[ℝ]
            TangentSpace hI.boundaryI y →L[ℝ] ℝ) x₀)
        ⟨x₀, inducedMetricInner (M := M) g x₀⟩).2 u v =
      ((inducedMetricInner (M := M) g x₀) u) v
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) x₀).linearMapAt ℝ x₀ _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ x₀ _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ)
    (B := BoundaryManifold I M) (F := ℝ) x₀]
  have h_symmL_id : ∀ w : hI.boundaryE,
      ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) w = w := by
    intro w
    have hsymmL_eq :
        (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀
          = mfderivWithin 𝓘(ℝ, hI.boundaryE) hI.boundaryI
              (extChartAt hI.boundaryI x₀).symm
              (Set.range hI.boundaryI) (extChartAt hI.boundaryI x₀ x₀) :=
      TangentBundle.symmL_trivializationAt hb_bdy
    rw [hsymmL_eq, mfderivWithin_range_extChartAt_symm]
    rfl
  have hcoe :
      ⇑((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀)
        = (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ :=
    funext fun w => Bundle.Trivialization.symmL_apply (R := ℝ)
      (e := _root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀)
      (_root_.FiberBundle.mem_baseSet_trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀) w
  have hsymm1 : (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ u
      = ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) u := by
    rw [hcoe]
  have hsymm2 : (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symm x₀ v
      = ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ x₀) v := by
    rw [hcoe]
  rw [hsymm1, hsymm2, h_symmL_id u, h_symmL_id v]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_basepoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_basepoint target :: scope.openDecls } }

private noncomputable def boundaryFlatChartedInv
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    (hI.boundaryE →L[ℝ] ℝ) →L[ℝ] hI.boundaryE :=
  ContinuousLinearMap.inverse (boundaryFlatCharted (M := M) g x₀ b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatChartedInv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatChartedInv target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatChartedInv_contMDiffAt
    (x₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, (hI.boundaryE →L[ℝ] ℝ) →L[ℝ] hI.boundaryE) ∞
      (boundaryFlatChartedInv (M := M) g x₀) x₀ := by
  have h_flat : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFlatCharted (M := M) g x₀) x₀ :=
    boundaryFlatCharted_contMDiffAt (M := M) g x₀
  have h_inv : (boundaryFlatCharted (M := M) g x₀ x₀).IsInvertible := by
    rw [boundaryFlatCharted_basepoint (M := M) g x₀]
    exact inducedMetricInner_isInvertible (M := M) g x₀
  have h_inverse_smooth :
      ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        (boundaryFlatCharted (M := M) g x₀ x₀) :=
    h_inv.contDiffAt_map_inverse
  exact h_inverse_smooth.contMDiffAt.comp x₀ h_flat

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatChartedInv_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatChartedInv_contMDiffAt target :: scope.openDecls } }

private noncomputable def boundaryFunOfInwardCharted
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] ℝ :=
  (boundaryFunOfInwardCLM (M := M) g b).comp
    ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) x₀).symmL ℝ b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCharted target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma boundaryFunOfInwardCharted_apply
    (x₀ : BoundaryManifold I M) (b : BoundaryManifold I M)
    (w : hI.boundaryE) :
    boundaryFunOfInwardCharted (M := M) g x₀ b w =
      g.inner (b : M) (inwardCoord (M := M) b)
        (boundaryInclusionMfderiv (M := M) b
          (((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) x₀).symmL ℝ b) w)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCharted_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardCharted_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_section_contMDiffOn
    (α₀ : BoundaryManifold I M) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M =>
        TotalSpace.mk' E y
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).symm y hI.inwardCoordE))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := by
  have hiff :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M))).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun y : M => (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).symm y
        hI.inwardCoordE)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => hI.inwardCoordE)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := contMDiffOn_const
  refine hconst.congr ?_
  intro y hy
  have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).apply_mk_symm hy
    hI.inwardCoordE
  exact congrArg Prod.snd h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_section_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_section_contMDiffOn target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ := by
  have hα_in : (α₀ : M) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  have h_section_open :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).baseSet ∈ 𝓝 (α₀ : M) :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).open_baseSet).mem_nhds hα_in
  have h_section_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M =>
        TotalSpace.mk' E y
          ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).symm y hI.inwardCoordE))
      (α₀ : M) :=
    (inwardCoordAt_section_contMDiffOn (M := M) α₀).contMDiffAt h_section_open
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  exact h_section_at.comp α₀ h_inclusion_at

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_section_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_section_contMDiffAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma chart_triv_second_inwardCoordAt
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb : (b : M) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).baseSet) :
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M))
        ⟨(b : M), inwardCoordAt (M := M) α₀ b⟩).2 = hI.inwardCoordE := by
  unfold inwardCoordAt
  have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).apply_mk_symm hb
    hI.inwardCoordE
  exact congrArg Prod.snd h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.chart_triv_second_inwardCoordAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.chart_triv_second_inwardCoordAt target :: scope.openDecls } }

private noncomputable def metricPullback
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    TangentSpace I (x : M) →ₗ[ℝ]
      (TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ) where
  toFun v :=
    { toFun := fun w => g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w)
      map_add' := fun u v' => by
        rw [ContinuousLinearMap.map_add (boundaryInclusionMfderiv (M := M) x) u v']
        exact ContinuousLinearMap.map_add (g.inner (x : M) v) _ _
      map_smul' := fun c v' => by
        rw [ContinuousLinearMap.map_smul (boundaryInclusionMfderiv (M := M) x) c v']
        exact ContinuousLinearMap.map_smul (g.inner (x : M) v) _ _ }
  map_add' v₁ v₂ := by
    ext w
    change g.inner (x : M) (v₁ + v₂) (boundaryInclusionMfderiv (M := M) x w) =
      g.inner (x : M) v₁ (boundaryInclusionMfderiv (M := M) x w) +
      g.inner (x : M) v₂ (boundaryInclusionMfderiv (M := M) x w)
    rw [map_add, add_apply]
  map_smul' c v := by
    ext w
    change g.inner (x : M) (c • v) (boundaryInclusionMfderiv (M := M) x w) =
      c • g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w)
    rw [map_smul, smul_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.metricPullback
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.metricPullback target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma metricPullback_apply
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) (w : TangentSpace hI.boundaryI x) :
    metricPullback (M := M) g x v w =
      g.inner (x : M) v (boundaryInclusionMfderiv (M := M) x w) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.metricPullback_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.metricPullback_apply target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma mem_ker_metricPullback_iff
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M)
    (v : TangentSpace I (x : M)) :
    v ∈ LinearMap.ker (metricPullback (M := M) g x) ↔
      v ∈ normalSubspace (M := M) g x := by
  refine ⟨?_, ?_⟩
  · intro hv w
    have h := congrArg (fun L : TangentSpace hI.boundaryI x →ₗ[ℝ] ℝ => L w) hv
    simp only [metricPullback_apply, LinearMap.zero_apply] at h
    exact h
  · intro hv
    apply LinearMap.ext
    intro w
    rw [metricPullback_apply, hv w]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mem_ker_metricPullback_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.mem_ker_metricPullback_iff target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma ker_metricPullback_eq_normalSubspace
    (g : SmoothRiemannianMetric I M) (x : BoundaryManifold I M) :
    LinearMap.ker (metricPullback (M := M) g x) = normalSubspace (M := M) g x := by
  apply Submodule.ext
  intro v
  exact mem_ker_metricPullback_iff (M := M) g x v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ker_metricPullback_eq_normalSubspace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.ker_metricPullback_eq_normalSubspace target :: scope.openDecls } }

variable (g : SmoothRiemannianMetric I M)

private noncomputable def boundaryFunOfInwardAtChartedCLM
    (α₀ : BoundaryManifold I M) (b : BoundaryManifold I M) :
    hI.boundaryE →L[ℝ] ℝ :=
  ((_root_.FiberBundle.trivializationAt (E →L[ℝ] ℝ)
        (fun y : M => TangentSpace I y →L[ℝ] ℝ) (α₀ : M))
    ⟨(b : M), g.inner (b : M) (inwardCoordAt (M := M) α₀ b)⟩).2.comp
    (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
      (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAtChartedCLM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAtChartedCLM target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFunOfInwardAtChartedCLM_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] ℝ) ∞
      (boundaryFunOfInwardAtChartedCLM (M := M) g α₀) α₀ := by
  have h_inwardCoord_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (inwardCoordAt (M := M) α₀ b)) α₀ :=
    inwardCoordAt_section_contMDiffAt (M := M) α₀
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_g_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          y (g.inner y)) := g.contMDiff
  have h_g_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b : M) (g.inner (b : M))) α₀ :=
    h_g_section.contMDiffAt.comp α₀ h_inclusion_at
  have h_inner_applied : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] ℝ)
          (b : M)
          (g.inner (b : M) (inwardCoordAt (M := M) α₀ b))) α₀ :=
    h_g_at.clm_bundle_apply h_inwardCoord_section
  have h_α_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (fun b : BoundaryManifold I M =>
        ((_root_.FiberBundle.trivializationAt (E →L[ℝ] ℝ)
            (fun y : M => TangentSpace I y →L[ℝ] ℝ) (α₀ : M))
          ⟨(b : M),
            g.inner (b : M) (inwardCoordAt (M := M) α₀ b)⟩).2) α₀ := by
    rw [Bundle.contMDiffAt_totalSpace] at h_inner_applied
    exact h_inner_applied.2
  have h_dincl_clm : ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE →L[ℝ] E) ∞
      (fun b : BoundaryManifold I M =>
        inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
          (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b) α₀ :=
    h_inclusion_at.mfderiv_const infty_le_top_add'
  exact h_α_smooth.clm_comp h_dincl_clm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAtChartedCLM_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAtChartedCLM_contMDiffAt target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFunOfInwardAtChartedCLM_apply_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source)
    (w : hI.boundaryE) :
    boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b w =
      g.inner (b : M) (inwardCoordAt (M := M) α₀ b)
        (boundaryInclusionMfderiv (M := M) b
          (((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
  unfold boundaryFunOfInwardAtChartedCLM
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply]
  have h_amb_baseSet : (b : M) ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb_amb
  rw [hom_trivializationAt_apply]
  have h_inC :
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M => ℝ)
        (α₀ : M) (b : M) (α₀ : M) (b : M)
        (g.inner (b : M) (inwardCoordAt (M := M) α₀ b)))
        (inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
          (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b w) =
        g.inner (b : M) (inwardCoordAt (M := M) α₀ b)
          (boundaryInclusionMfderiv (M := M) b
            (((_root_.FiberBundle.trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
    rw [ContinuousLinearMap.inCoordinates]
    rw [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply]
    have h_trivial_clmAt : ∀ x : ℝ,
        (_root_.FiberBundle.trivializationAt ℝ (fun _ : M => ℝ) (α₀ : M)).continuousLinearMapAt ℝ (b : M) x = x := by
      intro x
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ (b : M) x = x
      rw [Bundle.Trivial.continuousLinearMapAt_trivialization (𝕜 := ℝ) (B := M) (F := ℝ) (b : M)]
      rfl
    rw [h_trivial_clmAt]
    have h_dinclITC_val :
        inTangentCoordinates hI.boundaryI I id (boundaryInclusion I M)
            (mfderiv hI.boundaryI I (boundaryInclusion I M)) α₀ b w =
          (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
            (b : M) (boundaryInclusionMfderiv (M := M) b
              (((_root_.FiberBundle.trivializationAt hI.boundaryE
                  (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)) := by
      have := dinclITC_apply (M := M) α₀ hb_amb hb_bdy w
      unfold dinclITC at this
      exact this
    rw [h_dinclITC_val]
    have h_amb_round :
        (((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).symmL ℝ (b : M))
            ((_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
              (b : M)
              (boundaryInclusionMfderiv (M := M) b
                (((_root_.FiberBundle.trivializationAt hI.boundaryE
                    (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w)))) =
          boundaryInclusionMfderiv (M := M) b
            (((_root_.FiberBundle.trivializationAt hI.boundaryE
                (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w) :=
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).symmL_continuousLinearMapAt
        (R := ℝ) h_amb_baseSet (boundaryInclusionMfderiv (M := M) b
          (((_root_.FiberBundle.trivializationAt hI.boundaryE
              (TangentSpace hI.boundaryI) α₀).symmL ℝ b) w))
    rw [h_amb_round]
  exact h_inC

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAtChartedCLM_apply_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFunOfInwardAtChartedCLM_apply_of_mem target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_apply_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_bdy : b ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).baseSet)
    (u v : hI.boundaryE) :
    boundaryFlatCharted (M := M) g α₀ b u v =
      inducedMetricInner (M := M) g b
        ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) α₀).symm b u)
        ((_root_.FiberBundle.trivializationAt hI.boundaryE
            (TangentSpace hI.boundaryI) α₀).symm b v) := by
  unfold boundaryFlatCharted
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (𝕜 := ℝ) hb_bdy hb_bdy (Set.mem_univ _)]
  change (_root_.FiberBundle.trivializationAt ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ) α₀).linearMapAt ℝ b _ = _
  change (Bundle.Trivial.trivialization (BoundaryManifold I M) ℝ).linearMapAt ℝ b _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization (𝕜 := ℝ) (B := BoundaryManifold I M) (F := ℝ) b]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_apply_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_apply_of_mem target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_isInvertible_of_mem
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_bdy : b ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).baseSet) :
    (boundaryFlatCharted (M := M) g α₀ b).IsInvertible := by
  classical
  obtain ⟨L_cle, hL_eq⟩ := inducedMetricInner_isInvertible (M := M) g b
  let T : TangentSpace hI.boundaryI b ≃L[ℝ] hI.boundaryE :=
    (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearEquivAt ℝ b
      hb_bdy
  let φ : hI.boundaryE ≃L[ℝ] (hI.boundaryE →L[ℝ] ℝ) :=
    T.symm.trans (L_cle.trans (T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)))
  refine ⟨φ, ?_⟩
  ext u v
  change ((T.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (L_cle (T.symm u))) v = _
  simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply]
  have h_eq_LCle : (L_cle : TangentSpace hI.boundaryI b →L[ℝ]
      (TangentSpace hI.boundaryI b →L[ℝ] ℝ)) =
      inducedMetricInner (M := M) g b := hL_eq
  have h_lhs : L_cle (T.symm u) (T.symm v) =
      inducedMetricInner (M := M) g b (T.symm u) (T.symm v) := by
    rw [show L_cle (T.symm u) (T.symm v) =
        (L_cle : TangentSpace hI.boundaryI b →L[ℝ]
          (TangentSpace hI.boundaryI b →L[ℝ] ℝ)) (T.symm u) (T.symm v) from rfl]
    rw [h_eq_LCle]
  rw [h_lhs]
  have h_T_symm_u : (T.symm u : TangentSpace hI.boundaryI b) =
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b u := rfl
  have h_T_symm_v : (T.symm v : TangentSpace hI.boundaryI b) =
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b v := rfl
  rw [h_T_symm_u, h_T_symm_v]
  rw [boundaryFlatCharted_apply_of_mem (M := M) g α₀ hb_bdy u v]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_isInvertible_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_isInvertible_of_mem target :: scope.openDecls } }

private noncomputable def boundaryComponentOfInwardAtCharted
    (α₀ : BoundaryManifold I M) (b : BoundaryManifold I M) : hI.boundaryE :=
  (boundaryFlatChartedInv (M := M) g α₀ b)
    (boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAtCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAtCharted target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma boundaryComponentOfInwardAtCharted_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞
      (boundaryComponentOfInwardAtCharted (M := M) g α₀) α₀ :=
  (boundaryFlatChartedInv_contMDiffAt (M := M) g α₀).clm_apply
    (boundaryFunOfInwardAtChartedCLM_contMDiffAt (M := M) g α₀)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAtCharted_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAtCharted_contMDiffAt target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma boundaryFlatCharted_clmAt_bdy_BC_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    boundaryFlatCharted (M := M) g α₀ b
      ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b)) =
      boundaryFunOfInwardAtChartedCLM (M := M) g α₀ b := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hb_bdy_baseSet : b ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet := hb_bdy
  rw [boundaryFlatCharted_apply_of_mem (M := M) g α₀ hb_bdy_baseSet
    ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b)) v]
  have h_round_BC :
      ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b
          ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
            ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b))) =
        boundaryComponentOfInwardAt (M := M) g α₀ b := by
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
      (e := _root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀)
      hb_bdy_baseSet]
    exact (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI)
      α₀).symmL_continuousLinearMapAt
      (R := ℝ) hb_bdy_baseSet (boundaryComponentOfInwardAt (M := M) g α₀ b)
  rw [h_round_BC]
  rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α₀ b
    ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm b v)]
  rw [boundaryFunOfInwardAtChartedCLM_apply_of_mem (M := M) g α₀ hb_amb hb_bdy v]
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (e := _root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀)
    hb_bdy_baseSet]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_clmAt_bdy_BC_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryFlatCharted_clmAt_bdy_BC_eq target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma boundaryComponentOfInwardAtCharted_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    boundaryComponentOfInwardAtCharted (M := M) g α₀ b =
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
        ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b) := by
  unfold boundaryComponentOfInwardAtCharted boundaryFlatChartedInv
  have h_inv := boundaryFlatCharted_isInvertible_of_mem (M := M) g α₀ hb_bdy
  have h_eq := boundaryFlatCharted_clmAt_bdy_BC_eq (M := M) g α₀ hb_amb hb_bdy
  rw [← h_eq]
  exact (ContinuousLinearMap.IsInvertible.inverse_apply_eq h_inv).mpr rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAtCharted_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryComponentOfInwardAtCharted_eq target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma inwardTangentialPartAtCharted_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
      (fun b : BoundaryManifold I M =>
        dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b)) α₀ :=
  dinclITC_apply_contMDiffAt (M := M)
    (boundaryComponentOfInwardAtCharted_contMDiffAt (M := M) g α₀)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAtCharted_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAtCharted_contMDiffAt target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma inwardTangentialPartAtCharted_eq
    (α₀ : BoundaryManifold I M) {b : BoundaryManifold I M}
    (hb_amb : (b : M) ∈ (chartAt H (α₀ : M)).source)
    (hb_bdy : b ∈ (chartAt hI.boundaryH α₀).source) :
    dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b) =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M)).continuousLinearMapAt ℝ
        (b : M) (inwardTangentialPartAt (M := M) g α₀ b) := by
  rw [dinclITC_apply (M := M) α₀ hb_amb hb_bdy]
  rw [boundaryComponentOfInwardAtCharted_eq (M := M) g α₀ hb_amb hb_bdy]
  have hb_bdy_baseSet : b ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet := hb_bdy
  have h_round_bdy :
      (((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symmL ℝ b)
          ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).continuousLinearMapAt
            ℝ b (boundaryComponentOfInwardAt (M := M) g α₀ b))) =
        boundaryComponentOfInwardAt (M := M) g α₀ b := by
    have := (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI)
      α₀).symmL_continuousLinearMapAt
      (R := ℝ) hb_bdy_baseSet (boundaryComponentOfInwardAt (M := M) g α₀ b)
    simpa using this
  rw [h_round_bdy]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAtCharted_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardTangentialPartAtCharted_eq target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ := by
  classical
  set T_amb := _root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M) with hT_amb_def
  have hα_amb : (α₀ : M) ∈ T_amb.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine (T_amb.contMDiffAt_iff (n := ∞)
    (f := fun b : BoundaryManifold I M =>
      TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b))
    (IM := hI.boundaryI) (x₀ := α₀) ?_).mpr ?_
  · change (TotalSpace.mk' E (α₀ : M)
      (outwardDirAt (M := M) g α₀ α₀)) ∈ T_amb.source
    rw [Trivialization.mem_source]
    change (α₀ : M) ∈ T_amb.baseSet
    simp only [hT_amb_def]
    exact FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine ⟨?_, ?_⟩
  · convert (boundaryInclusion_contMDiff (I := I) (M := M)).contMDiffAt using 1
    funext b
    exact (boundaryInclusion_apply (I := I) (M := M) b).symm
  · have h_inwardTangChart_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b)) α₀ :=
      inwardTangentialPartAtCharted_contMDiffAt (M := M) g α₀
    have h_const : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun _ : BoundaryManifold I M => hI.inwardCoordE) α₀ := contMDiffAt_const
    have h_sub : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          dinclITC (M := M) α₀ b (boundaryComponentOfInwardAtCharted (M := M) g α₀ b) -
            hI.inwardCoordE) α₀ :=
      h_inwardTangChart_at.sub h_const
    refine h_sub.congr_of_eventuallyEq ?_
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        (b : M) ∈ (chartAt H (α₀ : M)).source := by
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact h_continuous.continuousAt.preimage_mem_nhds
        ((chartAt H (α₀ : M)).open_source.mem_nhds (mem_chart_source H _))
    have h_nhds_bdy : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        b ∈ (chartAt hI.boundaryH α₀).source :=
      (chartAt hI.boundaryH α₀).open_source.mem_nhds (mem_chart_source _ _)
    filter_upwards [h_nhds_amb, h_nhds_bdy] with b hb_amb hb_bdy
    have hb_amb_baseSet : (b : M) ∈ T_amb.baseSet := by
      simp only [hT_amb_def]
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hb_amb
    rw [show (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M) (outwardDirAt (M := M) g α₀ b) from ?_]
    swap
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [outwardDirAt_def, map_sub]
    rw [← inwardTangentialPartAtCharted_eq (M := M) g α₀ hb_amb hb_bdy]
    have h_inwardCoord_chartTriv :
        T_amb.continuousLinearMapAt ℝ (b : M) (inwardCoordAt (M := M) α₀ b) =
          hI.inwardCoordE := by
      rw [show T_amb.continuousLinearMapAt ℝ (b : M) (inwardCoordAt (M := M) α₀ b) =
          (T_amb ⟨(b : M), inwardCoordAt (M := M) α₀ b⟩).2 from ?_]
      · simp only [hT_amb_def]
        exact chart_triv_second_inwardCoordAt (M := M) α₀ hb_amb_baseSet
      · rw [Trivialization.continuousLinearMapAt_apply]
        rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [h_inwardCoord_chartTriv]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_section_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_section_contMDiffAt target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_norm_squared_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)) α₀ := by
  classical
  have h_outwardDir_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_section_contMDiffAt (M := M) g α₀
  have h_inclusion_at : ContMDiffAt hI.boundaryI I ∞ (boundaryInclusion I M) α₀ :=
    boundaryInclusion_contMDiff.contMDiffAt
  have h_g_section : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          y (g.inner y)) := g.contMDiff
  have h_g_at : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M =>
            TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b : M) (g.inner (b : M))) α₀ :=
    h_g_section.contMDiffAt.comp α₀ h_inclusion_at
  have h_apply : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' ℝ (E := fun y : M => ℝ)
          (b : M)
          (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b))) α₀ :=
    h_g_at.clm_bundle_apply₂ h_outwardDir_section h_outwardDir_section
  rw [Bundle.contMDiffAt_totalSpace] at h_apply
  exact h_apply.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_norm_squared_contMDiffAt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_norm_squared_contMDiffAt target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_norm_squared_pos_basepoint
    (α₀ : BoundaryManifold I M) :
    0 < g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
        (outwardDirAt (M := M) g α₀ α₀) := by
  rw [outwardDirAt_self (M := M) g α₀]
  exact g_inner_outwardDir_pos (M := M) g α₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_norm_squared_pos_basepoint
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_norm_squared_pos_basepoint target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
theorem outwardNormalAt_section_contMDiffAt
    (α₀ : BoundaryManifold I M) :
    ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g α₀ b)) α₀ := by
  classical
  have h_q_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_norm_squared_contMDiffAt (M := M) g α₀
  have h_q_pos_at : 0 < g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀) :=
    outwardDirAt_norm_squared_pos_basepoint (M := M) g α₀
  have h_q_ne : g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀) ≠ 0 := ne_of_gt h_q_pos_at
  have h_q_sqrt_at : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b))) α₀ := by
    have h_sqrt_at : ContDiffAt ℝ ∞ Real.sqrt
        (g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
          (outwardDirAt (M := M) g α₀ α₀)) := Real.contDiffAt_sqrt h_q_ne
    exact h_sqrt_at.contMDiffAt.comp α₀ h_q_smooth
  have h_sqrt_pos : 0 < Real.sqrt (g.inner (α₀ : M)
      (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀)) := Real.sqrt_pos.mpr h_q_pos_at
  have h_sqrt_ne : Real.sqrt (g.inner (α₀ : M) (outwardDirAt (M := M) g α₀ α₀)
      (outwardDirAt (M := M) g α₀ α₀)) ≠ 0 := ne_of_gt h_sqrt_pos
  have h_sqrt_inv_at : ContMDiffAt hI.boundaryI 𝓘(ℝ) ∞
      (fun b : BoundaryManifold I M =>
        (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)))⁻¹) α₀ :=
    h_q_sqrt_at.inv₀ h_sqrt_ne
  have h_outwardDir_section : ContMDiffAt hI.boundaryI (I.prod 𝓘(ℝ, E)) ∞
      (fun b : BoundaryManifold I M =>
        TotalSpace.mk' E (b : M) (outwardDirAt (M := M) g α₀ b)) α₀ :=
    outwardDirAt_section_contMDiffAt (M := M) g α₀
  set T_amb := _root_.FiberBundle.trivializationAt E (TangentSpace I) (α₀ : M) with hT_amb_def
  have hα_amb : (α₀ : M) ∈ T_amb.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine (T_amb.contMDiffAt_iff (n := ∞)
    (f := fun b : BoundaryManifold I M =>
      TotalSpace.mk' E (b : M) (outwardNormalAt (M := M) g α₀ b))
    (IM := hI.boundaryI) (x₀ := α₀) ?_).mpr ?_
  · change (TotalSpace.mk' E (α₀ : M)
      (outwardNormalAt (M := M) g α₀ α₀)) ∈ T_amb.source
    rw [Trivialization.mem_source]
    change (α₀ : M) ∈ T_amb.baseSet
    simp only [hT_amb_def]
    exact FiberBundle.mem_baseSet_trivializationAt' (α₀ : M)
  refine ⟨?_, ?_⟩
  · convert (boundaryInclusion_contMDiff (I := I) (M := M)).contMDiffAt using 1
    funext b
    exact (boundaryInclusion_apply (I := I) (M := M) b).symm
  · have h_outwardDirCharted_at : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2) α₀ := by
      rw [Bundle.contMDiffAt_totalSpace] at h_outwardDir_section
      exact h_outwardDir_section.2
    have h_smul_smooth : ContMDiffAt hI.boundaryI 𝓘(ℝ, E) ∞
        (fun b : BoundaryManifold I M =>
          (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ •
            (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2) α₀ :=
      h_sqrt_inv_at.smul h_outwardDirCharted_at
    refine h_smul_smooth.congr_of_eventuallyEq ?_
    have h_q_continuous : ContinuousAt
        (fun b : BoundaryManifold I M =>
          g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)) α₀ := h_q_smooth.continuousAt
    have h_q_pos_nhds : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        0 < g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b) := by
      filter_upwards [h_q_continuous (eventually_gt_nhds h_q_pos_at)] with b hb
      exact hb
    have h_nhds_amb : ∀ᶠ b : BoundaryManifold I M in 𝓝 α₀,
        (b : M) ∈ T_amb.baseSet := by
      have h_continuous : Continuous (fun b : BoundaryManifold I M => (b : M)) :=
        continuous_subtype_val
      exact h_continuous.continuousAt.preimage_mem_nhds (T_amb.open_baseSet.mem_nhds hα_amb)
    filter_upwards [h_q_pos_nhds, h_nhds_amb] with b hb_q_pos hb_amb_baseSet
    have h_norm_formula : outwardNormalAt (M := M) g α₀ b =
        (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b := by
      unfold outwardNormalAt
      rw [dif_pos hb_q_pos]
    rw [h_norm_formula]
    rw [show (T_amb ⟨(b : M), (Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
          (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M)
          ((Real.sqrt (g.inner (b : M) (outwardDirAt (M := M) g α₀ b)
            (outwardDirAt (M := M) g α₀ b)))⁻¹ • outwardDirAt (M := M) g α₀ b) from ?_]
    swap
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]
    rw [map_smul]
    rw [show (T_amb ⟨(b : M), outwardDirAt (M := M) g α₀ b⟩).2 =
        T_amb.continuousLinearMapAt ℝ (b : M) (outwardDirAt (M := M) g α₀ b) from ?_]
    · rw [Trivialization.continuousLinearMapAt_apply]
      rw [T_amb.coe_linearMapAt_of_mem hb_amb_baseSet]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_section_contMDiffAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_section_contMDiffAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_section_contMDiffAt ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_section_contMDiffAt
omit [FiniteDimensional ℝ E] in
private lemma metricPullback_surjective
    (g : SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Function.Surjective (metricPullback (M := M) g y) := by
  intro α
  set u : TangentSpace hI.boundaryI y :=
    (boundaryFlatMap (M := M) g y).symm α with hu_def
  refine ⟨boundaryInclusionMfderiv (M := M) y u, ?_⟩
  refine LinearMap.ext fun w => ?_
  rw [metricPullback_apply]
  rw [show g.inner (y : M) (boundaryInclusionMfderiv (M := M) y u)
    (boundaryInclusionMfderiv (M := M) y w) =
        inducedMetricInner (M := M) g y u w from
        (inducedMetricInner_apply g y u w).symm]
  rw [show inducedMetricInner (M := M) g y u w = boundaryFlatMap (M := M) g y u w from rfl]
  have h := (boundaryFlatMap (M := M) g y).apply_symm_apply α
  exact congrArg (fun L : TangentSpace hI.boundaryI y →ₗ[ℝ] ℝ => L w) h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.metricPullback_surjective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.metricPullback_surjective target :: scope.openDecls } }
private lemma finrank_ker_metricPullback_eq_one
    (g : SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Module.finrank ℝ (LinearMap.ker (metricPullback (M := M) g y)) = 1 := by
  by_cases hN : Nonempty hI.boundaryH
  · have := hN
    have h_rk_null :=
      LinearMap.finrank_range_add_finrank_ker (metricPullback (M := M) g y)
    have h_surj : Function.Surjective (metricPullback (M := M) g y) :=
      metricPullback_surjective (M := M) g y
    have h_range_top : LinearMap.range (metricPullback (M := M) g y) = ⊤ :=
      LinearMap.range_eq_top.mpr h_surj
    have h_finrank_range : Module.finrank ℝ
        (LinearMap.range (metricPullback (M := M) g y)) =
        Module.finrank ℝ (TangentSpace hI.boundaryI y →ₗ[ℝ] ℝ) := by
      rw [h_range_top, finrank_top]
    have h_dual : Module.finrank ℝ (TangentSpace hI.boundaryI y →ₗ[ℝ] ℝ) =
        Module.finrank ℝ (TangentSpace hI.boundaryI y) := Subspace.dual_finrank_eq
    have h_source : Module.finrank ℝ (TangentSpace I (y : M)) = Module.finrank ℝ E :=
      LinearEquiv.finrank_eq
        (tangentSpaceModelContinuousLinearEquiv (I := I) (y : M)).toLinearEquiv
    have h_boundary : Module.finrank ℝ (TangentSpace hI.boundaryI y) =
        Module.finrank ℝ hI.boundaryE :=
      LinearEquiv.finrank_eq
        (tangentSpaceModelContinuousLinearEquiv (I := hI.boundaryI) y).toLinearEquiv
    have h_codim : Module.finrank ℝ (TangentSpace hI.boundaryI y) + 1 =
        Module.finrank ℝ E := by
      rw [h_boundary]
      exact hI.finrank_boundaryE_succ
    rw [h_finrank_range, h_dual] at h_rk_null
    omega
  · have : IsEmpty hI.boundaryH := not_nonempty_iff.mp hN
    have : IsEmpty (BoundaryManifold I M) :=
      BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
    exact (IsEmpty.false y).elim

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.finrank_ker_metricPullback_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.finrank_ker_metricPullback_eq_one target :: scope.openDecls } }
theorem normalSubspace_finrank_one
    (g : SmoothRiemannianMetric I M) (y : BoundaryManifold I M) :
    Module.finrank ℝ (normalSubspace (M := M) g y) = 1 := by
  rw [← ker_metricPullback_eq_normalSubspace (M := M) g y]
  exact finrank_ker_metricPullback_eq_one (M := M) g y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace_finrank_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace_finrank_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace_finrank_one ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.normalSubspace_finrank_one

omit [FiniteDimensional ℝ E] hI in
private lemma unit_vectors_in_1dim_equal_or_opposite
    (g : SmoothRiemannianMetric I M) {y : BoundaryManifold I M}
    {V : Submodule ℝ (TangentSpace I (y : M))}
    (hV : Module.finrank ℝ V = 1)
    {v w : TangentSpace I (y : M)} (hv : v ∈ V) (hw : w ∈ V)
    (hv_unit : g.inner (y : M) v v = 1) (hw_unit : g.inner (y : M) w w = 1) :
    v = w ∨ v = -w := by
  classical
  let v' : V := ⟨v, hv⟩
  let w' : V := ⟨w, hw⟩
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0] at hv_unit
    simp at hv_unit
  have hv'_ne : v' ≠ 0 := by
    intro h0
    apply hv_ne
    exact congrArg Subtype.val h0
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one (K := ℝ) (V := V) hV hv'_ne w'
  have hc_amb : c • v = w := by
    have := congrArg Subtype.val hc
    simpa [v', w'] using this
  have h_g_w_w : g.inner (y : M) w w = c * c * g.inner (y : M) v v := by
    rw [show w = c • v from hc_amb.symm]
    rw [show g.inner (y : M) (c • v) = c • (g.inner (y : M) v) from
          map_smul _ _ _]
    rw [smul_apply, smul_eq_mul,
        ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  have hc_sq : c * c = 1 := by
    rw [hv_unit, mul_one] at h_g_w_w
    rw [h_g_w_w] at hw_unit
    exact hw_unit
  have hc_eq : c = 1 ∨ c = -1 := by
    have hc_sq_one : c ^ 2 = 1 := by rw [sq]; exact hc_sq
    exact sq_eq_one_iff.mp hc_sq_one
  rcases hc_eq with h_pos | h_neg
  · left
    rw [show w = c • v from hc_amb.symm, h_pos, one_smul]
  · right
    rw [show w = c • v from hc_amb.symm, h_neg, neg_one_smul, neg_neg]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.unit_vectors_in_1dim_equal_or_opposite
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.unit_vectors_in_1dim_equal_or_opposite target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M) :
    outwardDirAt (M := M) g α y = 0 ↔
      inwardCoordAt (M := M) α y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) := by
  refine ⟨?_, ?_⟩
  · intro h0
    rw [outwardDirAt_def, sub_eq_zero] at h0
    rw [← h0, inwardTangentialPartAt_def]
    exact ⟨boundaryComponentOfInwardAt (M := M) g α y, rfl⟩
  · rintro ⟨u, hu⟩
    rw [outwardDirAt_def, sub_eq_zero, inwardTangentialPartAt_def, ← hu]
    apply congrArg (boundaryInclusionMfderiv (M := M) y)
    have h_pair : ∀ w : TangentSpace hI.boundaryI y,
        inducedMetricInner (M := M) g y
          (boundaryComponentOfInwardAt (M := M) g α y) w =
        inducedMetricInner (M := M) g y u w := by
      intro w
      rw [inducedMetricInner_boundaryComponentOfInwardAt (M := M) g α y w]
      rw [inducedMetricInner_apply]
      rw [hu]
    have h_lin_eq : boundaryFlatLinear (M := M) g y
        (boundaryComponentOfInwardAt (M := M) g α y) =
        boundaryFlatLinear (M := M) g y u := by
      refine LinearMap.ext fun w => ?_
      rw [boundaryFlatLinear_apply, boundaryFlatLinear_apply]
      exact h_pair w
    exact boundaryFlatLinear_injective (M := M) g y h_lin_eq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardDirAt_ne_zero_of_transverse
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    outwardDirAt (M := M) g α y ≠ 0 := by
  intro h0
  exact h_trans
    ((outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α y).mp h0)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_ne_zero_of_transverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardDirAt_ne_zero_of_transverse target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma g_inner_outwardDirAt_pos_of_transverse
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) :=
  g.pos (y : M) _ (outwardDirAt_ne_zero_of_transverse (M := M) g α y h_trans)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_pos_of_transverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_pos_of_transverse target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    g.inner (y : M) (outwardDirAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) < 0 := by
  have hpos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have h_id : g.inner (y : M) (outwardDirAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) =
      -g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) := by
    rw [g_inner_outwardDirAt_inwardCoordAt (M := M) g α y,
        g_inner_outwardDirAt_outwardDirAt (M := M) g α y]
    ring
  rw [h_id]
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardNormalAt_norm_one_of_transverse
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    g.inner (y : M) (outwardNormalAt (M := M) g α y)
        (outwardNormalAt (M := M) g α y) = 1 := by
  set q : ℝ := g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y) with hq_def
  have hq_pos : 0 < q :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hsq_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hsq_ne : Real.sqrt q ≠ 0 := ne_of_gt hsq_pos
  have hsq_sq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq_pos.le
  have h_normal_eq : outwardNormalAt (M := M) g α y =
      (Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y := by
    unfold outwardNormalAt
    rw [dif_pos hq_pos]
  rw [h_normal_eq]
  have h1 : g.inner (y : M) ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y)
          ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
      (Real.sqrt q)⁻¹ • (g.inner (y : M) (outwardDirAt (M := M) g α y))
          ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) := by
    rw [show g.inner (y : M) ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
        (Real.sqrt q)⁻¹ • g.inner (y : M) (outwardDirAt (M := M) g α y) from
          map_smul _ _ _]
    rfl
  rw [h1]
  rw [show (g.inner (y : M) (outwardDirAt (M := M) g α y))
        ((Real.sqrt q)⁻¹ • outwardDirAt (M := M) g α y) =
      (Real.sqrt q)⁻¹ • g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) from
    ContinuousLinearMap.map_smul _ _ _]
  rw [show g.inner (y : M) (outwardDirAt (M := M) g α y)
        (outwardDirAt (M := M) g α y) = q from rfl]
  rw [smul_eq_mul, smul_eq_mul]
  rw [show (Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) = q / (Real.sqrt q * Real.sqrt q) by
    field_simp]
  rw [hsq_sq]
  exact div_self hq_ne

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_norm_one_of_transverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_norm_one_of_transverse target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardNormalAt_mem_normalSubspace
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M) :
    outwardNormalAt (M := M) g α y ∈ normalSubspace (M := M) g y := by
  unfold outwardNormalAt
  classical
  by_cases h_pos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)
  · rw [dif_pos h_pos]
    exact (normalSubspace (M := M) g y).smul_mem _
      (outwardDirAt_mem_normalSubspace (M := M) g α y)
  · rw [dif_neg h_pos]
    exact (normalSubspace (M := M) g y).zero_mem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_mem_normalSubspace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_mem_normalSubspace target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma outwardNormalAt_inner_inwardCoordAt_neg_of_transverse
    (g : SmoothRiemannianMetric I M) (α y : BoundaryManifold I M)
    (h_trans : inwardCoordAt (M := M) α y ∉ Set.range (boundaryInclusionMfderiv (M := M) y)) :
    g.inner (y : M) (outwardNormalAt (M := M) g α y)
        (inwardCoordAt (M := M) α y) < 0 := by
  have hq_pos : 0 < g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y) :=
    g_inner_outwardDirAt_pos_of_transverse (M := M) g α y h_trans
  have h_normal_eq : outwardNormalAt (M := M) g α y =
      (Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
          (outwardDirAt (M := M) g α y)))⁻¹ • outwardDirAt (M := M) g α y := by
    unfold outwardNormalAt
    rw [dif_pos hq_pos]
  rw [h_normal_eq]
  rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  have hsq_pos : 0 < Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)) := Real.sqrt_pos.mpr hq_pos
  have hsq_inv_pos : 0 < (Real.sqrt (g.inner (y : M) (outwardDirAt (M := M) g α y)
      (outwardDirAt (M := M) g α y)))⁻¹ := inv_pos.mpr hsq_pos
  have hneg : g.inner (y : M) (outwardDirAt (M := M) g α y)
      (inwardCoordAt (M := M) α y) < 0 :=
    g_inner_outwardDirAt_inwardCoordAt_neg_of_transverse (M := M) g α y h_trans
  exact mul_neg_of_pos_of_neg hsq_inv_pos hneg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_inner_inwardCoordAt_neg_of_transverse
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_inner_inwardCoordAt_neg_of_transverse target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_mem_range_iff_of_orientation
    (α₀ α₁ y : BoundaryManifold I M)
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    inwardCoordAt (M := M) α₀ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) ↔
      inwardCoordAt (M := M) α₁ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y) := by
  have h_range_eq : Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap =
      Set.range (boundaryInclusionMfderiv (M := M) y) := rfl
  rw [h_range_eq] at h_w
  rcases h_w with ⟨w', hw'⟩
  have hc_ne : c ≠ 0 := ne_of_gt hc
  refine ⟨fun h₀ => ?_, fun h₁ => ?_⟩
  · rcases h₀ with ⟨u, hu⟩
    refine ⟨c⁻¹ • (u - w'), ?_⟩
    have h_target : (c : ℝ) • inwardCoordAt (M := M) α₁ y =
        (boundaryInclusionMfderiv (M := M) y) u - (boundaryInclusionMfderiv (M := M) y) w' := by
      rw [hu, hw']; abel
    have h_inv_smul : (c : ℝ)⁻¹ • ((c : ℝ) • inwardCoordAt (M := M) α₁ y) =
        inwardCoordAt (M := M) α₁ y := by
      rw [← _root_.SemigroupAction.mul_smul, inv_mul_cancel₀ hc_ne, one_smul]
    have h_target_inv : inwardCoordAt (M := M) α₁ y =
        (c : ℝ)⁻¹ • ((boundaryInclusionMfderiv (M := M) y) u - (boundaryInclusionMfderiv (M := M) y)
          w') := by
      rw [← h_inv_smul, h_target]
    rw [h_target_inv, ContinuousLinearMap.map_smul, map_sub]
  · rcases h₁ with ⟨u, hu⟩
    refine ⟨c • u + w', ?_⟩
    rw [map_add, ContinuousLinearMap.map_smul, hu]
    set vw : TangentSpace I (y : M) := boundaryInclusionMfderiv (M := M) y w' with hvw_def
    change (c : ℝ) • inwardCoordAt (M := M) α₁ y + vw = inwardCoordAt (M := M) α₀ y
    have hw'' : vw = inwardCoordAt (M := M) α₀ y -
        (c : ℝ) • inwardCoordAt (M := M) α₁ y := hw'
    rw [hw'']; abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_mem_range_iff_of_orientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_mem_range_iff_of_orientation target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma inwardCoordAt_not_mem_range_iff_of_orientation
    (α₀ α₁ y : BoundaryManifold I M)
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    inwardCoordAt (M := M) α₀ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y) ↔
      inwardCoordAt (M := M) α₁ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y) := by
  rw [not_iff_not]
  exact inwardCoordAt_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_not_mem_range_iff_of_orientation
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.inwardCoordAt_not_mem_range_iff_of_orientation target :: scope.openDecls } }
omit [FiniteDimensional ℝ E] in
private lemma g_inner_outwardNormalAt_inwardCoordAt_other_neg
    (g : SmoothRiemannianMetric I M) (α₀ α₁ y : BoundaryManifold I M)
    (h_trans₁ : inwardCoordAt (M := M) α₁ y ∉ Set.range (boundaryInclusionMfderiv (M := M) y))
    (c : ℝ) (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (inwardCoordAt (M := M) α₀ y) < 0 := by
  have h_range_eq : Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap =
      Set.range (boundaryInclusionMfderiv (M := M) y) := rfl
  rw [h_range_eq] at h_w
  rcases h_w with ⟨w', hw'⟩
  set N₁ : TangentSpace I (y : M) := outwardNormalAt (M := M) g α₁ y with hN₁_def
  set v₀ : TangentSpace I (y : M) := inwardCoordAt (M := M) α₀ y with hv₀_def
  set v₁ : TangentSpace I (y : M) := inwardCoordAt (M := M) α₁ y with hv₁_def
  set vw : TangentSpace I (y : M) := boundaryInclusionMfderiv (M := M) y w' with hvw_def
  have hw'' : vw = v₀ - c • v₁ := hw'
  have hv₀_eq : v₀ = c • v₁ + vw := by rw [hw'']; abel
  rw [hv₀_eq, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, smul_eq_mul]
  have h_orth : g.inner (y : M) N₁ vw = 0 := by
    rw [hvw_def]
    exact (outwardNormalAt_mem_normalSubspace (M := M) g α₁ y) w'
  rw [h_orth, add_zero]
  have h_neg : g.inner (y : M) N₁ v₁ < 0 :=
    outwardNormalAt_inner_inwardCoordAt_neg_of_transverse (M := M) g α₁ y h_trans₁
  exact mul_neg_of_pos_of_neg hc h_neg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardNormalAt_inwardCoordAt_other_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.g_inner_outwardNormalAt_inwardCoordAt_other_neg target :: scope.openDecls } }
theorem outwardNormalAt_chart_invariance_of_orientation
    (g : SmoothRiemannianMetric I M) (α₀ α₁ y : BoundaryManifold I M)
    {c : ℝ} (hc : 0 < c)
    (h_w : inwardCoordAt (M := M) α₀ y - c • inwardCoordAt (M := M) α₁ y ∈
        Set.range (boundaryInclusionMfderiv (M := M) y).toLinearMap) :
    outwardNormalAt (M := M) g α₀ y = outwardNormalAt (M := M) g α₁ y := by
  classical
  by_cases h_trans₁ : inwardCoordAt (M := M) α₁ y ∈ Set.range (boundaryInclusionMfderiv (M := M) y)
  · have h_trans₀ : inwardCoordAt (M := M) α₀ y ∈ Set.range
      (boundaryInclusionMfderiv (M := M) y) := by
      have h_iff := inwardCoordAt_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
      exact h_iff.mpr h_trans₁
    have h0_α₀ : outwardDirAt (M := M) g α₀ y = 0 :=
      (outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α₀ y).mpr h_trans₀
    have h0_α₁ : outwardDirAt (M := M) g α₁ y = 0 :=
      (outwardDirAt_eq_zero_iff_inwardCoordAt_mem_range (M := M) g α₁ y).mpr h_trans₁
    have h_q_α₀ : g.inner (y : M) (outwardDirAt (M := M) g α₀ y)
        (outwardDirAt (M := M) g α₀ y) = 0 := by
      rw [h0_α₀]; simp
    have h_q_α₁ : g.inner (y : M) (outwardDirAt (M := M) g α₁ y)
        (outwardDirAt (M := M) g α₁ y) = 0 := by
      rw [h0_α₁]; simp
    have h_normal_α₀ : outwardNormalAt (M := M) g α₀ y = 0 := by
      unfold outwardNormalAt
      rw [dif_neg]
      rw [h_q_α₀]; exact lt_irrefl 0
    have h_normal_α₁ : outwardNormalAt (M := M) g α₁ y = 0 := by
      unfold outwardNormalAt
      rw [dif_neg]
      rw [h_q_α₁]; exact lt_irrefl 0
    rw [h_normal_α₀, h_normal_α₁]
  · have h_trans₁_ne : inwardCoordAt (M := M) α₁ y ∉ Set.range
      (boundaryInclusionMfderiv (M := M) y) :=
      h_trans₁
    have h_trans₀_ne : inwardCoordAt (M := M) α₀ y ∉ Set.range
      (boundaryInclusionMfderiv (M := M) y) := by
      have h_iff := inwardCoordAt_not_mem_range_iff_of_orientation (M := M) α₀ α₁ y c hc h_w
      exact h_iff.mpr h_trans₁_ne
    have hN₀_mem : outwardNormalAt (M := M) g α₀ y ∈ normalSubspace (M := M) g y :=
      outwardNormalAt_mem_normalSubspace (M := M) g α₀ y
    have hN₁_mem : outwardNormalAt (M := M) g α₁ y ∈ normalSubspace (M := M) g y :=
      outwardNormalAt_mem_normalSubspace (M := M) g α₁ y
    have hN₀_unit : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
        (outwardNormalAt (M := M) g α₀ y) = 1 :=
      outwardNormalAt_norm_one_of_transverse (M := M) g α₀ y h_trans₀_ne
    have hN₁_unit : g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (outwardNormalAt (M := M) g α₁ y) = 1 :=
      outwardNormalAt_norm_one_of_transverse (M := M) g α₁ y h_trans₁_ne
    have h_finrank : Module.finrank ℝ (normalSubspace (M := M) g y) = 1 :=
      normalSubspace_finrank_one (M := M) g y
    have h_eq_or_neg :=
      unit_vectors_in_1dim_equal_or_opposite (M := M) g h_finrank hN₀_mem hN₁_mem
        hN₀_unit hN₁_unit
    have h_sign : g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
        (inwardCoordAt (M := M) α₀ y) < 0 :=
      g_inner_outwardNormalAt_inwardCoordAt_other_neg (M := M) g α₀ α₁ y
        h_trans₁_ne c hc h_w
    have h_sign₀ : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
        (inwardCoordAt (M := M) α₀ y) < 0 :=
      outwardNormalAt_inner_inwardCoordAt_neg_of_transverse (M := M) g α₀ y h_trans₀_ne
    rcases h_eq_or_neg with h_eq | h_neg_eq
    · exact h_eq
    · exfalso
      have h_contra : g.inner (y : M) (outwardNormalAt (M := M) g α₀ y)
          (inwardCoordAt (M := M) α₀ y) =
          -g.inner (y : M) (outwardNormalAt (M := M) g α₁ y)
            (inwardCoordAt (M := M) α₀ y) := by
        rw [h_neg_eq]
        rw [show g.inner (y : M) (-outwardNormalAt (M := M) g α₁ y) =
              -g.inner (y : M) (outwardNormalAt (M := M) g α₁ y) from
            map_neg _ _]
        rfl
      rw [h_contra] at h_sign₀
      linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_chart_invariance_of_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_chart_invariance_of_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_chart_invariance_of_orientation ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.outwardNormalAt_chart_invariance_of_orientation

end Smoothness

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
