import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Gradient
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.GradientLaplacian.Green
import Submission.DifferentialGeometry.Geometry.Operator.WithBoundary.Laplacian
import Submission.DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.Riemannian
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open _root_.Submission.DifferentialGeometry.Geometry.Operator.WithBoundary

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpaceEuclideanSpaceRealFin_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instBorelSpace_differentialGeometry target :: scope.openDecls } }

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.I_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.I_half target :: scope.openDecls } }

structure InteriorSmoothScalar (g : SmoothRiemannianMetric (I_half n) M) where
  toFun : M → ℝ
  smooth : ContMDiff (I_half n) 𝓘(ℝ, ℝ) ∞ toFun
  interior_support : tsupport toFun ⊆ (I_half n).interior M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar

namespace InteriorSmoothScalar

variable {g : SmoothRiemannianMetric (I_half n) M}

@[ext] theorem ext {f h : InteriorSmoothScalar g} (hfh : f.toFun = h.toFun) : f = h := by
  cases f; cases h; congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.ext ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.ext

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instZero : Zero (InteriorSmoothScalar g) where
  zero :=
    { toFun := fun _ => 0
      smooth := contMDiff_const
      interior_support := by
        simp [tsupport] }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instZero ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instZero

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAdd : Add (InteriorSmoothScalar g) where
  add f h :=
    { toFun := f.toFun + h.toFun
      smooth := f.smooth.add h.smooth
      interior_support := by
        refine (tsupport_add (f := f.toFun) (g := h.toFun)).trans ?_
        exact Set.union_subset f.interior_support h.interior_support }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAdd ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAdd

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instNeg : Neg (InteriorSmoothScalar g) where
  neg f :=
    { toFun := -f.toFun
      smooth := f.smooth.neg
      interior_support := by
        rw [tsupport_neg]
        exact f.interior_support }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instNeg ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instNeg

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSub : Sub (InteriorSmoothScalar g) where
  sub f h :=
    { toFun := f.toFun - h.toFun
      smooth := f.smooth.sub h.smooth
      interior_support := by
        have h_eq : f.toFun - h.toFun = f.toFun + (-h.toFun) := by
          funext x; ring_nf
        rw [h_eq]
        refine (tsupport_add (f := f.toFun) (g := -h.toFun)).trans ?_
        refine Set.union_subset f.interior_support ?_
        rw [tsupport_neg]
        exact h.interior_support }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSub ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSub

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulReal : SMul ℝ (InteriorSmoothScalar g) where
  smul c f :=
    { toFun := c • f.toFun
      smooth := by
        have h : (c • f.toFun) = (fun x : M => c * f.toFun x) := by
          funext x; rfl
        rw [h]
        exact contMDiff_const.mul f.smooth
      interior_support := by
        have h_support : Function.support (c • f.toFun) ⊆ Function.support f.toFun := by
          intro x hx hx_zero
          apply hx
          change c * f.toFun x = 0
          rw [hx_zero, _root_.MulZeroClass.mul_zero]
        have h_tsupp : tsupport (c • f.toFun) ⊆ tsupport f.toFun :=
          closure_mono h_support
        exact h_tsupp.trans f.interior_support }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulReal ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulReal

@[simp] lemma toFun_zero : (0 : InteriorSmoothScalar g).toFun = (fun _ : M => 0) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero

@[simp] lemma toFun_zero_apply (x : M) : (0 : InteriorSmoothScalar g).toFun x = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zero_apply

@[simp] lemma toFun_add (f h : InteriorSmoothScalar g) :
    (f + h).toFun = f.toFun + h.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add

@[simp] lemma toFun_add_apply (f h : InteriorSmoothScalar g) (x : M) :
    (f + h).toFun x = f.toFun x + h.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_add_apply

@[simp] lemma toFun_neg (f : InteriorSmoothScalar g) :
    (-f).toFun = -f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg

@[simp] lemma toFun_neg_apply (f : InteriorSmoothScalar g) (x : M) :
    (-f).toFun x = -f.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_neg_apply

@[simp] lemma toFun_sub (f h : InteriorSmoothScalar g) :
    (f - h).toFun = f.toFun - h.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub

@[simp] lemma toFun_sub_apply (f h : InteriorSmoothScalar g) (x : M) :
    (f - h).toFun x = f.toFun x - h.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_sub_apply

@[simp] lemma toFun_smul (c : ℝ) (f : InteriorSmoothScalar g) :
    (c • f).toFun = c • f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul

@[simp] lemma toFun_smul_apply (c : ℝ) (f : InteriorSmoothScalar g) (x : M) :
    (c • f).toFun x = c * f.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_smul_apply

lemma toFun_injective :
    Function.Injective (fun f : InteriorSmoothScalar g => f.toFun) := by
  intro f h hfh
  exact ext hfh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_injective ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_injective

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulNat : SMul ℕ (InteriorSmoothScalar g) := ⟨nsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulNat ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulNat
instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulInt : SMul ℤ (InteriorSmoothScalar g) := ⟨zsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulInt ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instSMulInt

@[simp] lemma toFun_nsmul (f : InteriorSmoothScalar g) (k : ℕ) :
    (k • f).toFun = k • f.toFun := by
  induction k with
  | zero =>
    change (nsmulRec 0 f).toFun = (0 : ℕ) • f.toFun
    change (0 : InteriorSmoothScalar g).toFun = (0 : ℕ) • f.toFun
    rw [toFun_zero, zero_nsmul]
    rfl
  | succ k ih =>
    change (nsmulRec (k + 1) f).toFun = (k + 1) • f.toFun
    change (nsmulRec k f + f).toFun = (k + 1) • f.toFun
    have hk : (nsmulRec k f).toFun = k • f.toFun := ih
    rw [toFun_add, hk, succ_nsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_nsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_nsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_nsmul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_nsmul

@[simp] lemma toFun_zsmul (f : InteriorSmoothScalar g) (z : ℤ) :
    (z • f).toFun = z • f.toFun := by
  rcases z with k | k
  · change (k • f).toFun = (Int.ofNat k) • f.toFun
    rw [toFun_nsmul]; simp
  · change (-((k + 1) • f)).toFun = (Int.negSucc k) • f.toFun
    rw [toFun_neg, toFun_nsmul]
    show -((k + 1) • f.toFun) = Int.negSucc k • f.toFun
    rw [show (Int.negSucc k : ℤ) = -((k + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zsmul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFun_zsmul

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAddCommGroup : AddCommGroup (InteriorSmoothScalar g) :=
  toFun_injective.addCommGroup
    (fun f => f.toFun)
    toFun_zero
    toFun_add
    toFun_neg
    toFun_sub
    toFun_nsmul
    toFun_zsmul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAddCommGroup ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instAddCommGroup

def toFunAddHom : InteriorSmoothScalar g →+ (M → ℝ) where
  toFun := fun f => f.toFun
  map_zero' := toFun_zero
  map_add' := toFun_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFunAddHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFunAddHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFunAddHom ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.toFunAddHom

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instModuleReal : Module ℝ (InteriorSmoothScalar g) :=
  toFun_injective.module ℝ toFunAddHom toFun_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instModuleReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instModuleReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instModuleReal ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.instModuleReal

end InteriorSmoothScalar

variable [T2Space M] [CompactSpace M]

omit [CompactSpace M] in
omit [T2Space M] in
lemma InteriorSmoothScalar.continuous_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x ((gradGWithBoundarySection
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I_half n) g
    (gradGWithBoundarySection (I := I_half n) g f.smooth f.interior_support)
    (gradGWithBoundarySection (I := I_half n) g h.smooth h.interior_support)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_inner_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_inner_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_inner_grad ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_inner_grad

omit [T2Space M] [CompactSpace M] in
lemma InteriorSmoothScalar.continuous_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    Continuous (fun x : M => f.toFun x * h.toFun x) :=
  f.smooth.continuous.mul h.smooth.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.continuous_mul

lemma InteriorSmoothScalar.integrable_mul
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    _root_.MeasureTheory.Integrable (fun x : M => f.toFun x * h.toFun x)
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  exact (f.continuous_mul h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_mul

lemma InteriorSmoothScalar.integrable_inner_grad
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    _root_.MeasureTheory.Integrable (fun x : M =>
        g.inner x ((gradGWithBoundarySection
              (I := I_half n) g f.smooth f.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((gradGWithBoundarySection
              (I := I_half n) g h.smooth h.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x))
      (riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I_half n) (M := M) g
  exact (f.continuous_inner_grad h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_inner_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_inner_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_inner_grad ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integrable_inner_grad

def interiorSmoothScalarH1Inner
    {g : SmoothRiemannianMetric (I_half n) M}
    (f h : InteriorSmoothScalar g) : ℝ :=
  (∫ x, f.toFun x * h.toFun x
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
  (∫ x, g.inner x ((gradGWithBoundarySection
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner


lemma interiorSmoothScalarH1Inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner f h =
      (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x ((gradGWithBoundarySection
                (I := I_half n) g f.smooth f.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((gradGWithBoundarySection
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_def ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_def


lemma interiorSmoothScalarH1Inner_symm
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner f h = interiorSmoothScalarH1Inner h f := by
  unfold interiorSmoothScalarH1Inner
  congr 1
  · refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact mul_comm _ _
  · refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_symm


lemma InteriorSmoothScalar.integral_mul_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    0 ≤ ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine _root_.MeasureTheory.integral_nonneg ?_
  intro x
  exact mul_self_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_mul_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_mul_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_mul_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_mul_self_nonneg

omit [T2Space M] [CompactSpace M] in
lemma SmoothRiemannianMetric_inner_self_nonneg
    (g : SmoothRiemannianMetric (I_half n) M) (x : M)
    (v : TangentSpace (I_half n) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp [map_zero]
  · exact (g.pos x v hv).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.SmoothRiemannianMetric_inner_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.SmoothRiemannianMetric_inner_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.SmoothRiemannianMetric_inner_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.SmoothRiemannianMetric_inner_self_nonneg


lemma InteriorSmoothScalar.integral_inner_grad_self_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    0 ≤ ∫ x, g.inner x ((gradGWithBoundarySection
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((gradGWithBoundarySection
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g) := by
  refine _root_.MeasureTheory.integral_nonneg ?_
  intro x
  exact SmoothRiemannianMetric_inner_self_nonneg g x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_inner_grad_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_inner_grad_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_inner_grad_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.integral_inner_grad_self_nonneg


lemma interiorSmoothScalarH1Inner_nonneg
    {g : SmoothRiemannianMetric (I_half n) M} (f : InteriorSmoothScalar g) :
    0 ≤ interiorSmoothScalarH1Inner f f := by
  unfold interiorSmoothScalarH1Inner
  exact add_nonneg f.integral_mul_self_nonneg f.integral_inner_grad_self_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_nonneg

omit [CompactSpace M] in
omit [T2Space M] in
@[simp] lemma InteriorSmoothScalar.grad_g_with_boundary_section_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (f : InteriorSmoothScalar g) (x : M) :
    (gradGWithBoundarySection
        (I := I_half n) g f.smooth f.interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x =
      gradFun (I := I_half n) g f.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_apply

omit [CompactSpace M] in
omit [T2Space M] in
lemma InteriorSmoothScalar.grad_g_with_boundary_section_add_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ : InteriorSmoothScalar g) (x : M) :
    (gradGWithBoundarySection
        (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x =
      ((gradGWithBoundarySection
            (I := I_half n) g f₁.smooth f₁.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) +
      ((gradGWithBoundarySection
            (I := I_half n) g f₂.smooth f₂.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) := by
  rw [InteriorSmoothScalar.grad_g_with_boundary_section_apply,
    InteriorSmoothScalar.grad_g_with_boundary_section_apply,
    InteriorSmoothScalar.grad_g_with_boundary_section_apply]
  have hfun : (f₁ + f₂).toFun = f₁.toFun + f₂.toFun := rfl
  rw [hfun]
  exact gradFun_add (I := I_half n) g
    (f₁.smooth.mdifferentiable (by simp) x)
    (f₂.smooth.mdifferentiable (by simp) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_add_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_add_apply

lemma interiorSmoothScalar_integral_mul_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : InteriorSmoothScalar g) :
    (∫ x, (f₁ + f₂).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, f₁.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, f₂.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, (f₁ + f₂).toFun x * h.toFun x =
      f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x := by
    intro x
    rw [InteriorSmoothScalar.toFun_add_apply]
    ring
  rw [show (fun x : M => (f₁ + f₂).toFun x * h.toFun x) =
      (fun x : M => f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x) from
      funext hpt]
  exact _root_.MeasureTheory.integral_add (f₁.integrable_mul h) (f₂.integrable_mul h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_add_left

lemma interiorSmoothScalar_integral_inner_grad_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : InteriorSmoothScalar g) :
    (∫ x, g.inner x ((gradGWithBoundarySection
              (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((gradGWithBoundarySection
              (I := I_half n) g h.smooth h.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      (∫ x, g.inner x ((gradGWithBoundarySection
                (I := I_half n) g f₁.smooth f₁.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((gradGWithBoundarySection
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) +
      (∫ x, g.inner x ((gradGWithBoundarySection
                (I := I_half n) g f₂.smooth f₂.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((gradGWithBoundarySection
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : ∀ x : M, g.inner x
      ((gradGWithBoundarySection
          (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((gradGWithBoundarySection
          (I := I_half n) g h.smooth h.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x) =
      g.inner x
        ((gradGWithBoundarySection
            (I := I_half n) g f₁.smooth f₁.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) +
      g.inner x
        ((gradGWithBoundarySection
            (I := I_half n) g f₂.smooth f₂.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) := by
    intro x
    rw [InteriorSmoothScalar.grad_g_with_boundary_section_add_apply f₁ f₂ x]
    rw [map_add, add_apply]
  rw [show (fun x : M => g.inner x
      ((gradGWithBoundarySection
          (I := I_half n) g (f₁ + f₂).smooth (f₁ + f₂).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((gradGWithBoundarySection
          (I := I_half n) g h.smooth h.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        ((gradGWithBoundarySection
            (I := I_half n) g f₁.smooth f₁.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x) +
      g.inner x
        ((gradGWithBoundarySection
            (I := I_half n) g f₂.smooth f₂.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) from funext hpt]
  exact _root_.MeasureTheory.integral_add (f₁.integrable_inner_grad h) (f₂.integrable_inner_grad h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_add_left

lemma interiorSmoothScalarH1Inner_add_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (f₁ f₂ h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner (f₁ + f₂) h =
      interiorSmoothScalarH1Inner f₁ h + interiorSmoothScalarH1Inner f₂ h := by
  unfold interiorSmoothScalarH1Inner
  rw [interiorSmoothScalar_integral_mul_add_left,
    interiorSmoothScalar_integral_inner_grad_add_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_add_left

omit [CompactSpace M] in
omit [T2Space M] in
lemma InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f : InteriorSmoothScalar g) (x : M) :
    (gradGWithBoundarySection
        (I := I_half n) g (c • f).smooth (c • f).interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x =
      c • ((gradGWithBoundarySection
        (I := I_half n) g f.smooth f.interior_support :
      Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
        (TangentSpace (I_half n) : M → Type _)⟯) x) := by
  rw [InteriorSmoothScalar.grad_g_with_boundary_section_apply,
    InteriorSmoothScalar.grad_g_with_boundary_section_apply]
  apply metricFlatLinear_injective (I := I_half n) g x
  ext v
  change g.inner x (gradFun (I := I_half n) g (c • f.toFun) x) v =
    g.inner x (c • gradFun (I := I_half n) g f.toFun x) v
  rw [inner_gradFun (I := I_half n) g (c • f.toFun) x v]
  rw [show g.inner x (c • gradFun (I := I_half n) g f.toFun x) v =
      c * g.inner x (gradFun (I := I_half n) g f.toFun x) v from ?_]
  swap
  · rw [map_smul, smul_apply, smul_eq_mul]
  rw [inner_gradFun (I := I_half n) g f.toFun x v]
  set d_f : TangentSpace (I_half n) x →L[ℝ] ℝ := mfderiv (I_half n) 𝓘(ℝ, ℝ) f.toFun x
    with hd_f_def
  have hHaf : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) f.toFun x d_f := by
    rw [hd_f_def]
    exact (f.smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hHa_smul : HasMFDerivAt (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x (c • d_f) :=
    hHaf.const_smul c
  have hd_smul : mfderiv (I_half n) 𝓘(ℝ, ℝ) (c • f.toFun) x = c • d_f :=
    hHa_smul.mfderiv
  rw [hd_smul]
  change (c • d_f) v = c * d_f v
  rw [smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply


lemma interiorSmoothScalar_integral_mul_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : InteriorSmoothScalar g) :
    (∫ x, (c • f).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => (c • f).toFun x * h.toFun x) =
      (fun x : M => c * (f.toFun x * h.toFun x)) := by
    funext x; rw [InteriorSmoothScalar.toFun_smul_apply]; ring
  rw [hpt]
  rw [_root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_mul_smul_left


lemma interiorSmoothScalar_integral_inner_grad_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : InteriorSmoothScalar g) :
    (∫ x, g.inner x ((gradGWithBoundarySection
              (I := I_half n) g (c • f).smooth (c • f).interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
          ((gradGWithBoundarySection
              (I := I_half n) g h.smooth h.interior_support :
            Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
              (TangentSpace (I_half n) : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) =
      c * (∫ x, g.inner x ((gradGWithBoundarySection
                (I := I_half n) g f.smooth f.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
            ((gradGWithBoundarySection
                (I := I_half n) g h.smooth h.interior_support :
              Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
                (TangentSpace (I_half n) : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I_half n) (M := M) g)) := by
  have hpt : (fun x : M => g.inner x
      ((gradGWithBoundarySection
          (I := I_half n) g (c • f).smooth (c • f).interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)
      ((gradGWithBoundarySection
          (I := I_half n) g h.smooth h.interior_support :
        Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
          (TangentSpace (I_half n) : M → Type _)⟯) x)) =
      (fun x : M => c * g.inner x
        ((gradGWithBoundarySection
            (I := I_half n) g f.smooth f.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)
        ((gradGWithBoundarySection
            (I := I_half n) g h.smooth h.interior_support :
          Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
            (TangentSpace (I_half n) : M → Type _)⟯) x)) := by
    funext x
    rw [InteriorSmoothScalar.grad_g_with_boundary_section_smul_apply c f x]
    rw [map_smul, smul_apply, smul_eq_mul]
  rw [hpt, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalar_integral_inner_grad_smul_left


lemma interiorSmoothScalarH1Inner_smul_left
    {g : SmoothRiemannianMetric (I_half n) M}
    (c : ℝ) (f h : InteriorSmoothScalar g) :
    interiorSmoothScalarH1Inner (c • f) h =
      c * interiorSmoothScalarH1Inner f h := by
  unfold interiorSmoothScalarH1Inner
  rw [interiorSmoothScalar_integral_mul_smul_left,
    interiorSmoothScalar_integral_inner_grad_smul_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.interiorSmoothScalarH1Inner_smul_left

noncomputable instance instPreInnerProductSpaceCoreInteriorSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    PreInnerProductSpace.Core ℝ (InteriorSmoothScalar g) where
  inner f h := interiorSmoothScalarH1Inner f h
  conj_inner_symm f h := by
    change (interiorSmoothScalarH1Inner h f : ℝ) =
      interiorSmoothScalarH1Inner f h
    exact interiorSmoothScalarH1Inner_symm h f
  re_inner_nonneg f := by
    change (0 : ℝ) ≤ interiorSmoothScalarH1Inner f f
    exact interiorSmoothScalarH1Inner_nonneg f
  add_left f₁ f₂ h := by
    change interiorSmoothScalarH1Inner (f₁ + f₂) h =
      interiorSmoothScalarH1Inner f₁ h + interiorSmoothScalarH1Inner f₂ h
    exact interiorSmoothScalarH1Inner_add_left f₁ f₂ h
  smul_left f h c := by
    change interiorSmoothScalarH1Inner (c • f) h =
      c * interiorSmoothScalarH1Inner f h
    exact interiorSmoothScalarH1Inner_smul_left c f h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instPreInnerProductSpaceCoreInteriorSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.instPreInnerProductSpaceCoreInteriorSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instPreInnerProductSpaceCoreInteriorSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instPreInnerProductSpaceCoreInteriorSmoothScalar

noncomputable instance instSeminormedAddCommGroupInteriorSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    SeminormedAddCommGroup (InteriorSmoothScalar g) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instSeminormedAddCommGroupInteriorSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.instSeminormedAddCommGroupInteriorSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instSeminormedAddCommGroupInteriorSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instSeminormedAddCommGroupInteriorSmoothScalar

noncomputable instance instInnerProductSpaceInteriorSmoothScalar
    {g : SmoothRiemannianMetric (I_half n) M} :
    InnerProductSpace ℝ (InteriorSmoothScalar g) :=
  InnerProductSpace.ofCore _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instInnerProductSpaceInteriorSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.instInnerProductSpaceInteriorSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.instInnerProductSpaceInteriorSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.instInnerProductSpaceInteriorSmoothScalar

@[simp] lemma InteriorSmoothScalar.inner_def
    {g : SmoothRiemannianMetric (I_half n) M} (f h : InteriorSmoothScalar g) :
    @_root_.Inner.inner ℝ _ _ f h = interiorSmoothScalarH1Inner f h := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.inner_def ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.InteriorSmoothScalar.inner_def

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
