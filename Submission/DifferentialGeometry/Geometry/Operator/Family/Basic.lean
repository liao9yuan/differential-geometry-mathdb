import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import Submission.DifferentialGeometry.Geometry.Metric.Family.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Scalar.Calculus

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tangentSpace_finiteDimensional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tangentSpace_finiteDimensional target :: scope.openDecls } }

def gradientAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : TangentSpace I x :=
  gradientFun (I := I) (G.metric t) f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.gradientAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.gradientAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.gradientAt ``Submission.DifferentialGeometry.Geometry.Curvature.gradientAt

def divergenceAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  divergence (I := I) (G.connection t) X x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.divergenceAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.divergenceAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.divergenceAt ``Submission.DifferentialGeometry.Geometry.Curvature.divergenceAt

def laplacianAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacian (I := I) (G.connection t) (G.metric t) f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt

def driftTerm
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  (G.metric t).inner x (X x) (gradientAt (I := I) G t f x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm

def heatOperatorWithDrift
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x + driftTerm (I := I) G t X f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift

def heatOperator
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperator ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperator

@[simp] theorem driftTerm_zero_drift
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    driftTerm (I := I) G t (fun y : M => (0 : TangentSpace I y)) f x = 0 := by
  simp [driftTerm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_zero_drift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_zero_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_zero_drift ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_zero_drift

@[simp] theorem heatOperator_eq_laplacianAt
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperator (I := I) G t f x = laplacianAt (I := I) G t f x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperator_eq_laplacianAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperator_eq_laplacianAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperator_eq_laplacianAt ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperator_eq_laplacianAt

theorem heatOperatorWithDrift_zero_drift
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) f x =
      heatOperator (I := I) G t f x := by
  simp [heatOperatorWithDrift, heatOperator]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_zero_drift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_zero_drift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_zero_drift ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_zero_drift

section FamilyAlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_sub_const
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real) {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (fun y : M => f y - c) x =
      driftTerm (I := I) G t X f x := by
  unfold driftTerm gradientAt
  rw [gradientFun_sub (I := I) (G.metric t) hf mdifferentiableAt_const]
  rw [gradientFun_const]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_sub_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_sub_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_sub_const ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_sub_const

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_const_smul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (a • f) x =
      a * driftTerm (I := I) G t X f x := by
  unfold driftTerm gradientAt
  rw [gradientFun_const_smul (I := I) (G.metric t) a hf]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_const_smul ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_const_smul

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_add
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    driftTerm (I := I) G t X (fun y : M => f y + h y) x =
      driftTerm (I := I) G t X f x +
        driftTerm (I := I) G t X h x := by
  unfold driftTerm gradientAt
  rw [gradientFun_add (I := I) (G.metric t) hf hh]
  simp only [map_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_add ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_add

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_sub
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    driftTerm (I := I) G t X (fun y : M => f y - h y) x =
      driftTerm (I := I) G t X f x -
        driftTerm (I := I) G t X h x := by
  unfold driftTerm gradientAt
  rw [gradientFun_sub (I := I) (G.metric t) hf hh]
  simp only [map_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_sub ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_sub

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem heatOperatorWithDrift_sub_const
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y - c) x =
      heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift laplacianAt
  rw [laplacian_sub_const (I := I) (G.connection t) (G.metric t) c hf x]
  rw [driftTerm_sub_const (I := I) G t X c (hf x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_const ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_const

theorem heatOperatorWithDrift_const_smul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    heatOperatorWithDrift (I := I) G t X (a • f) x =
      a * heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift laplacianAt
  rw [laplacian_const_smul (I := I) (G.connection t) (G.metric t) a hf hgrad]
  rw [driftTerm_const_smul (I := I) G t X a (hf x)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_const_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_const_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_const_smul ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_const_smul

theorem laplacianAt_sub
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y - h y) x =
      laplacianAt (I := I) G t f x -
        laplacianAt (I := I) G t h x := by
  unfold laplacianAt
  exact laplacian_sub (I := I) (G.connection t) (G.metric t)
    hf hh hgradf hgradh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_sub ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_sub

theorem laplacianAt_sub_at
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y - h y) x =
      laplacianAt (I := I) G t f x -
        laplacianAt (I := I) G t h x := by
  unfold laplacianAt
  exact laplacian_sub_at (I := I) (G.connection t) (G.metric t)
    hf hh hgradf hgradh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_sub_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_sub_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_sub_at ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_sub_at

theorem heatOperatorWithDrift_sub_at
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y - h y) x =
      heatOperatorWithDrift (I := I) G t X f x -
        heatOperatorWithDrift (I := I) G t X h x := by
  unfold heatOperatorWithDrift
  rw [laplacianAt_sub_at (I := I) G t hf hh hgradf hgradh]
  rw [driftTerm_sub (I := I) G t X (hf.self_of_nhds) (hh.self_of_nhds)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_at ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_sub_at

theorem laplacianAt_smul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (a • f) x =
      a * laplacianAt (I := I) G t f x := by
  unfold laplacianAt
  exact laplacian_const_smul (I := I) (G.connection t) (G.metric t)
    a hf hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_smul ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_smul

theorem laplacianAt_add
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y + h y) x =
      laplacianAt (I := I) G t f x +
        laplacianAt (I := I) G t h x := by
  unfold laplacianAt laplacian
  have hgradient :
      gradientFun (I := I) (G.metric t) (fun z : M => f z + h z) =
        gradientFun (I := I) (G.metric t) f +
          gradientFun (I := I) (G.metric t) h := by
    funext y
    exact gradientFun_add (I := I) (G.metric t) (hf y) (hh y)
  rw [hgradient]
  exact divergence_add (I := I) (G.connection t) inferInstance hgradf hgradh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_add ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_add
omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem gradientAt_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientAt (I := I) G t (fun y : M => f y * h y) x =
      f x • gradientAt (I := I) G t h x +
        h x • gradientAt (I := I) G t f x := by
  unfold gradientAt
  exact gradientFun_mul (I := I) (G.metric t) hf hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.gradientAt_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.gradientAt_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.gradientAt_mul ``Submission.DifferentialGeometry.Geometry.Curvature.gradientAt_mul

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem driftTerm_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    driftTerm (I := I) G t X (fun y : M => f y * h y) x =
      f x * driftTerm (I := I) G t X h x +
        h x * driftTerm (I := I) G t X f x := by
  unfold driftTerm
  rw [gradientAt_mul (I := I) G t hf hh]
  simp only [map_add, map_smul, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_mul ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_mul

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem gradientAt_rpow
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientAt (I := I) G t (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) • gradientAt (I := I) G t f x := by
  unfold gradientAt
  exact gradientFun_rpow (I := I) (G.metric t) p hf hpos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.gradientAt_rpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.gradientAt_rpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.gradientAt_rpow ``Submission.DifferentialGeometry.Geometry.Curvature.gradientAt_rpow

theorem laplacianAt_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x)
    (hfgradh : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) h y)) x)
    (hhgradf : MDiffAt (T% (h • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y * h y) x =
      f x * laplacianAt (I := I) G t h x +
        h x * laplacianAt (I := I) G t f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x) := by
  unfold laplacianAt gradientAt
  exact laplacian_mul (I := I) (G.connection t) (G.metric t)
    hf hh hgradf hgradh hfgradh hhgradf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_mul ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_mul

theorem laplacianAt_mul_of_scalarRegular
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y)
    (hgradh : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) h z) y) :
    laplacianAt (I := I) G t (fun y : M => f y * h y) x =
      f x * laplacianAt (I := I) G t h x +
        h x * laplacianAt (I := I) G t f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x) := by
  exact laplacianAt_mul (I := I) G t
    hf hh (hgradf x) (hgradh x)
    ((hf x).smul_section (hgradh x))
    ((hh x).smul_section (hgradf x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_mul_of_scalarRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_mul_of_scalarRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_mul_of_scalarRegular ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_mul_of_scalarRegular

omit [VectorBundle ℝ E (TangentSpace I : M → Type _)] in
theorem heatDrift_comp
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {φ : Real -> Real} {f : M -> Real} {x : M}
    (hφ : Differentiable Real φ)
    (hφ' : DifferentiableAt Real (deriv φ) (f x))
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    heatOperatorWithDrift (I := I) G t X
        (fun y : M => φ (f y)) x =
      deriv φ (f x) * heatOperatorWithDrift (I := I) G t X f x +
        deriv (deriv φ) (f x) *
          (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t f x) := by
  unfold heatOperatorWithDrift laplacianAt driftTerm gradientAt
  rw [laplacian_comp (I := I) (G.connection t) (G.metric t)
    hφ hφ' hf hgrad]
  rw [gradientFun_comp (I := I) (G.metric t) (hφ (f x)) (hf x)]
  simp only [map_smul, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatDrift_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatDrift_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatDrift_comp ``Submission.DifferentialGeometry.Geometry.Curvature.heatDrift_comp

theorem heatDrift_mul
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y)
    (hgradh : forall y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) h z) y) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y * h y) x =
      f x * heatOperatorWithDrift (I := I) G t X h x +
        h x * heatOperatorWithDrift (I := I) G t X f x +
          2 * (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t h x) := by
  unfold heatOperatorWithDrift
  rw [laplacianAt_mul_of_scalarRegular (I := I) G t hf hh hgradf hgradh]
  rw [driftTerm_mul (I := I) G t X (hf x) (hh x)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatDrift_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatDrift_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatDrift_mul ``Submission.DifferentialGeometry.Geometry.Curvature.heatDrift_mul

theorem heatDrift_add
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y + h y) x =
      heatOperatorWithDrift (I := I) G t X f x +
        heatOperatorWithDrift (I := I) G t X h x := by
  unfold heatOperatorWithDrift
  rw [laplacianAt_add (I := I) G t hf hh hgradf hgradh]
  rw [driftTerm_add (I := I) G t X (hf x) (hh x)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatDrift_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatDrift_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatDrift_add ``Submission.DifferentialGeometry.Geometry.Curvature.heatDrift_add

theorem laplacianAt_rpow
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M} (p : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacianAt (I := I) G t f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          (G.metric t).inner x
            (gradientAt (I := I) G t f x)
            (gradientAt (I := I) G t f x) := by
  unfold laplacianAt gradientAt
  exact laplacian_rpow (I := I) (G.connection t) (G.metric t)
    p hf hpos hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_rpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_rpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_rpow ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_rpow

theorem laplacianAt_sq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x) := by
  have hhalf :=
    half_laplacian_mul_self
      (I := I) (G.connection t) (G.metric t) (f := f) (x := x)
      hf_all hf_x hgrad hfg
  unfold laplacianAt gradientAt
  have hpow :
      (fun y : M => f y ^ 2) = fun y : M => f y * f y := by
    funext y
    ring
  rw [hpow]
  have hmain :
      laplacian (I := I) (G.connection t) (G.metric t)
          (fun y : M => f y * f y) x =
        2 * (f x * laplacian (I := I) (G.connection t) (G.metric t) f x +
          (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) f x)
            (gradientFun (I := I) (G.metric t) f x)) := by
    linarith
  rw [hmain]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_sq ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_sq

theorem laplacianAt_sq_of_scalarRegular
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : ∀ y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x) := by
  exact laplacianAt_sq (I := I) G t
    hf (hf x) (hgrad x)
    (scalar_mul_grad_mdiffAt (I := I) (G.metric t) hf hgrad)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_sq_of_scalarRegular then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_sq_of_scalarRegular"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_sq_of_scalarRegular ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_sq_of_scalarRegular

end FamilyAlgebraicRules

@[simp] theorem gradientAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    gradientAt (I := I) G t f x = gradientFun (I := I) (G.metric t) f x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.gradientAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.gradientAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.gradientAt_eq ``Submission.DifferentialGeometry.Geometry.Curvature.gradientAt_eq

omit [FiniteDimensional ℝ E] in
@[simp] theorem divergenceAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) :
    divergenceAt (I := I) G t X x =
      divergence (I := I) (G.connection t) X x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.divergenceAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.divergenceAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.divergenceAt_eq ``Submission.DifferentialGeometry.Geometry.Curvature.divergenceAt_eq

@[simp] theorem laplacianAt_eq
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    laplacianAt (I := I) G t f x =
      laplacian (I := I) (G.connection t) (G.metric t) f x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_eq ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_eq

theorem driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X f x = 0 := by
  unfold driftTerm gradientAt
  rw [gradientFun_eq_zero_at_spatial_min_of_isInteriorPoint
    (I := I) (G.metric t) hmin hx hf]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint

theorem driftTerm_eq_zero_at_spatial_min
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X f x = 0 :=
  driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint
    (I := I) G t X hmin BoundarylessManifold.isInteriorPoint hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min ``Submission.DifferentialGeometry.Geometry.Curvature.driftTerm_eq_zero_at_spatial_min

def laplacianNonnegativeAtSpatialMinFamily
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time,
    LaplacianNonnegativeAtSpatialMin (I := I) (G.connection t) (G.metric t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianNonnegativeAtSpatialMinFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianNonnegativeAtSpatialMinFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianNonnegativeAtSpatialMinFamily ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianNonnegativeAtSpatialMinFamily

theorem laplacian_nonnegative_at_spatial_min_family
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time) :
    laplacianNonnegativeAtSpatialMinFamily (I := I) G := by
  intro t
  exact laplacianNonnegativeAtSpatialMin_of_metricCompatible (I := I)
    (G.connection t) (G.metric t) (G.metricCompatible t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacian_nonnegative_at_spatial_min_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacian_nonnegative_at_spatial_min_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacian_nonnegative_at_spatial_min_family ``Submission.DifferentialGeometry.Geometry.Curvature.laplacian_nonnegative_at_spatial_min_family

theorem laplacianAt_nonpos_at_spatial_max
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hmax : IsLocalMax f x)
    (hf : ContMDiff I 𝓘(Real, Real) ∞ f) :
    laplacianAt (I := I) G t f x <= 0 := by
  have hmdiff : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y :=
    fun y => hf.mdifferentiable (by simp) y
  have hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x :=
    gradientFun_mdiffAt (I := I) (G.metric t) hf x
  have hneggrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (-f) y) x := by
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (-f) y) =
          (T% fun y : M => -gradientFun (I := I) (G.metric t) f y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : _root_.Bundle.TotalSpace E (TangentSpace I : M -> Type _)))
      exact gradientFun_neg (I := I) (G.metric t) (hmdiff y)
    rw [heq]
    exact mdifferentiableAt_neg_section hgrad
  have hneg : 0 <= laplacianAt (I := I) G t (-f) x :=
    laplacian_nonneg_at_spatial_min_of_metricCompatible
      (I := I) (G.connection t) (G.metric t) (G.metricCompatible t)
      hmax.neg (hmdiff x).neg (Filter.Eventually.of_forall (fun y => (hmdiff y).neg)) hneggrad
  have hlin := laplacianAt_smul (I := I) G t (-1 : Real) hmdiff hgrad
  have hfun : (-f) = (-1 : Real) • f := by
    funext y
    simp
  rw [hfun, hlin] at hneg
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max

theorem laplacianAt_smul_at
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (a : Real) {f : M → Real} {x : M}
    (hf : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (a • f) x = a * laplacianAt (I := I) G t f x := by
  unfold laplacianAt
  exact laplacian_smul_at (I := I) (G.connection t) (G.metric t) a hf hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_smul_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_smul_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_smul_at ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_smul_at

theorem laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) {f : M → Real} {x : M}
    (hmax : IsLocalMax f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t f x ≤ 0 := by
  have hneggrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (-f) y) x := by
    have heq : (fun y : M => gradientFun (I := I) (G.metric t) (-f) y) =ᶠ[nhds x]
        (fun y : M => -gradientFun (I := I) (G.metric t) f y) := by
      filter_upwards [hf_near] with y hy
      exact gradientFun_neg (I := I) (G.metric t) hy
    have htotal :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (-f) y) =ᶠ[nhds x]
          (T% fun y : M => -gradientFun (I := I) (G.metric t) f y) := by
      filter_upwards [heq] with y hy
      change TotalSpace.mk' E y (gradientFun (I := I) (G.metric t) (-f) y) =
        TotalSpace.mk' E y (-gradientFun (I := I) (G.metric t) f y)
      rw [hy]
    exact (mdifferentiableAt_neg_section hgrad).congr_of_eventuallyEq htotal
  have hneg : 0 ≤ laplacianAt (I := I) G t (-f) x := by
    unfold laplacianAt
    exact laplacian_nonneg_at_spatial_min_of_metricCompatible_of_isInteriorPoint
      (I := I) (G.connection t) (G.metric t) (G.metricCompatible t)
      hmax.neg hx hf.neg (hf_near.mono (fun _y hy => hy.neg)) hneggrad
  have hlin := laplacianAt_smul_at (I := I) G t (-1 : Real) hf_near hgrad
  have hfun : (-f) = (-1 : Real) • f := by
    funext y
    simp
  rw [hfun, hlin] at hneg
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint ``Submission.DifferentialGeometry.Geometry.Curvature.laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint

theorem heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hx : I.IsInteriorPoint x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift
  rw [driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint
    (I := I) G t X hmin hx hf, add_zero]
  exact laplacian_nonneg_at_spatial_min_of_metricCompatible_of_isInteriorPoint
    (I := I) (G.connection t) (G.metric t) (G.metricCompatible t)
      hmin hx hf hf_near hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint

theorem heatOperatorWithDrift_at_spatial_min_nonneg
    [I.Boundaryless]
    (G : MetricConnectionFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x :=
  heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
    (I := I) G t X hmin BoundarylessManifold.isInteriorPoint hf hf_near hgrad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg ``Submission.DifferentialGeometry.Geometry.Curvature.heatOperatorWithDrift_at_spatial_min_nonneg

end

end DifferentialGeometry.Geometry.Curvature
