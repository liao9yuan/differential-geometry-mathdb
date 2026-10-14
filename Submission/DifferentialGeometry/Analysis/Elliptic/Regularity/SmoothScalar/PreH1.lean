import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import Submission.DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.CompactSupport
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

structure SmoothScalar (g : SmoothRiemannianMetric I M) where
  toFun : M → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar

namespace SmoothScalar

variable {g : SmoothRiemannianMetric I M}

def toContMDiffMap (f : SmoothScalar g) : C^∞⟮I, M; ℝ⟯ :=
  ⟨f.toFun, f.smooth⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContMDiffMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContMDiffMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContMDiffMap ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toContMDiffMap

omit [Module.Finite ℝ E] in
@[simp]
theorem coe_toContMDiffMap (f : SmoothScalar g) :
    ⇑f.toContMDiffMap = f.toFun :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.coe_toContMDiffMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.coe_toContMDiffMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.coe_toContMDiffMap ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.coe_toContMDiffMap

omit [Module.Finite ℝ E] in
@[ext] theorem ext {f h : SmoothScalar g} (hfh : f.toFun = h.toFun) : f = h := by
  cases f; cases h; congr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.ext ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.ext

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instZero : Zero (SmoothScalar g) where
  zero := { toFun := fun _ => 0, smooth := contMDiff_const }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instZero ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instZero

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAdd : Add (SmoothScalar g) where
  add f h := { toFun := f.toFun + h.toFun, smooth := f.smooth.add h.smooth }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAdd ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAdd

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instNeg : Neg (SmoothScalar g) where
  neg f := { toFun := -f.toFun, smooth := f.smooth.neg }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instNeg ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instNeg

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSub : Sub (SmoothScalar g) where
  sub f h := { toFun := f.toFun - h.toFun, smooth := f.smooth.sub h.smooth }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSub ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSub

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulReal : SMul ℝ (SmoothScalar g) where
  smul c f :=
    { toFun := c • f.toFun
      smooth := by
        have h : (c • f.toFun) = (fun x : M => c * f.toFun x) := by
          funext x; rfl
        rw [h]
        exact contMDiff_const.mul f.smooth }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulReal ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulReal

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_zero : (0 : SmoothScalar g).toFun = (fun _ : M => 0) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_zero_apply (x : M) : (0 : SmoothScalar g).toFun x = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zero_apply

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_add (f h : SmoothScalar g) :
    (f + h).toFun = f.toFun + h.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_add_apply (f h : SmoothScalar g) (x : M) :
    (f + h).toFun x = f.toFun x + h.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_add_apply

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_neg (f : SmoothScalar g) :
    (-f).toFun = -f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_neg_apply (f : SmoothScalar g) (x : M) :
    (-f).toFun x = -f.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_neg_apply

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_sub (f h : SmoothScalar g) :
    (f - h).toFun = f.toFun - h.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_sub_apply (f h : SmoothScalar g) (x : M) :
    (f - h).toFun x = f.toFun x - h.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_sub_apply

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_smul (c : ℝ) (f : SmoothScalar g) :
    (c • f).toFun = c • f.toFun := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_smul_apply (c : ℝ) (f : SmoothScalar g) (x : M) :
    (c • f).toFun x = c * f.toFun x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_smul_apply

omit [Module.Finite ℝ E] in
lemma toFun_injective :
    Function.Injective (fun f : SmoothScalar g => f.toFun) := by
  intro f h hfh
  exact ext hfh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_injective ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_injective

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulNat : SMul ℕ (SmoothScalar g) := ⟨nsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulNat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulNat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulNat ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulNat
instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulInt : SMul ℤ (SmoothScalar g) := ⟨zsmulRec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulInt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulInt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulInt ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instSMulInt

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_nsmul (f : SmoothScalar g) (n : ℕ) :
    (n • f).toFun = n • f.toFun := by
  induction n with
  | zero =>
    change (nsmulRec 0 f).toFun = (0 : ℕ) • f.toFun
    change (0 : SmoothScalar g).toFun = (0 : ℕ) • f.toFun
    rw [toFun_zero, zero_nsmul]
    rfl
  | succ n ih =>
    change (nsmulRec (n + 1) f).toFun = (n + 1) • f.toFun
    change (nsmulRec n f + f).toFun = (n + 1) • f.toFun
    have hn : (nsmulRec n f).toFun = n • f.toFun := ih
    rw [toFun_add, hn, succ_nsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_nsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_nsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_nsmul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_nsmul

omit [Module.Finite ℝ E] in
@[simp] lemma toFun_zsmul (f : SmoothScalar g) (z : ℤ) :
    (z • f).toFun = z • f.toFun := by
  rcases z with n | n
  · change (n • f).toFun = (Int.ofNat n) • f.toFun
    rw [toFun_nsmul]; simp
  · change (-((n + 1) • f)).toFun = (Int.negSucc n) • f.toFun
    rw [toFun_neg, toFun_nsmul]
    show -((n + 1) • f.toFun) = Int.negSucc n • f.toFun
    rw [show (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) from rfl,
      neg_zsmul, natCast_zsmul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zsmul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFun_zsmul

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAddCommGroup : AddCommGroup (SmoothScalar g) :=
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
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAddCommGroup ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instAddCommGroup

def toFunAddHom : SmoothScalar g →+ (M → ℝ) where
  toFun := fun f => f.toFun
  map_zero' := toFun_zero
  map_add' := toFun_add

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFunAddHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFunAddHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFunAddHom ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.toFunAddHom

instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instModuleReal : Module ℝ (SmoothScalar g) :=
  toFun_injective.module ℝ toFunAddHom toFun_smul

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instModuleReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instModuleReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instModuleReal ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.instModuleReal

end SmoothScalar

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
lemma SmoothScalar.continuous_inner_grad
    {g : SmoothRiemannianMetric I M} (f h : SmoothScalar g) :
    Continuous (fun x : M =>
      g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) :=
  TangentBundle.continuous_g_inner_of_smooth_sections (I := I) g
    (gradG (I := I) g ⟨f.toFun, f.smooth⟩) (gradG (I := I) g ⟨h.toFun, h.smooth⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_inner_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_inner_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_inner_grad ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_inner_grad

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
def SmoothScalar.gradientSqSup
    {g : SmoothRiemannianMetric I M} (f : SmoothScalar g) : ℝ :=
  _root_.Max.max (_root_.SupSet.sSup (Set.range (fun x : M =>
    g.inner x
      (gradFun (I := I) g f.toFun x)
      (gradFun (I := I) g f.toFun x)))) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem SmoothScalar.gradientSqSup_nonneg
    {g : SmoothRiemannianMetric I M} (f : SmoothScalar g) :
    0 ≤ f.gradientSqSup :=
  le_max_right _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_nonneg

omit [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem SmoothScalar.gradientSqSup_le
    {g : SmoothRiemannianMetric I M} (f : SmoothScalar g) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : ∀ x : M,
      g.inner x
          (gradFun (I := I) g f.toFun x)
          (gradFun (I := I) g f.toFun x) ≤ B) :
    f.gradientSqSup ≤ B := by
  unfold gradientSqSup
  apply max_le
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hrange : Set.range (fun x : M =>
          g.inner x
            (gradFun (I := I) g f.toFun x)
            (gradFun (I := I) g f.toFun x)) = (∅ : Set ℝ) := by
        rw [Set.range_eq_empty_iff]
        exact hM
      rw [hrange, Real.sSup_empty]
      exact hB
    · let _ : Nonempty M := hM
      apply csSup_le (Set.range_nonempty _)
      intro b hb
      obtain ⟨x, rfl⟩ := hb
      exact hbound x
  · exact hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_le ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.gradientSqSup_le

omit [T2Space M] in
theorem SmoothScalar.inner_grad_self_le_gradientSqSup
    {g : SmoothRiemannianMetric I M} (f : SmoothScalar g) (x : M) :
    g.inner x
        (gradFun (I := I) g f.toFun x)
        (gradFun (I := I) g f.toFun x) ≤
      f.gradientSqSup := by
  have hcontinuous : Continuous (fun y : M =>
      g.inner y
        (gradFun (I := I) g f.toFun y)
        (gradFun (I := I) g f.toFun y)) := by
    exact (f.continuous_inner_grad f).congr (fun _ => rfl)
  exact (le_csSup (isCompact_range hcontinuous).bddAbove
    (Set.mem_range_self x)).trans (le_max_left _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_grad_self_le_gradientSqSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_grad_self_le_gradientSqSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_grad_self_le_gradientSqSup ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_grad_self_le_gradientSqSup

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma SmoothScalar.continuous_mul {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    Continuous (fun x : M => f.toFun x * h.toFun x) :=
  f.smooth.continuous.mul h.smooth.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.continuous_mul

omit [I.Boundaryless] in
lemma SmoothScalar.integrable_mul {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    _root_.MeasureTheory.Integrable (fun x : M => f.toFun x * h.toFun x)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have _ : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f.continuous_mul h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_mul ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_mul

lemma SmoothScalar.integrable_inner_grad {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    _root_.MeasureTheory.Integrable (fun x : M =>
        g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have _ : _root_.MeasureTheory.IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact (f.continuous_inner_grad h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_inner_grad then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_inner_grad"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_inner_grad ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integrable_inner_grad

def smoothScalarH1Inner {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) : ℝ :=
  (∫ x, f.toFun x * h.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
  (∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner

lemma smoothScalarH1Inner_def {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) f h =
      (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_def ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_def

lemma smoothScalarH1Inner_symm {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) f h =
      smoothScalarH1Inner (I := I) (M := M) h f := by
  unfold smoothScalarH1Inner
  congr 1
  · refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x; exact mul_comm _ _
  · refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    exact g.symm x _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_symm ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_symm

omit [I.Boundaryless] in
lemma SmoothScalar.integral_mul_self_nonneg {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    0 ≤ ∫ x, f.toFun x * f.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  refine _root_.MeasureTheory.integral_nonneg ?_
  intro x
  exact mul_self_nonneg _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_mul_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_mul_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_mul_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_mul_self_nonneg

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [CompactSpace M] in
lemma SmoothRiemannianMetric_inner_self_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv
    simp [map_zero]
  · exact (g.pos x v hv).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothRiemannianMetric_inner_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothRiemannianMetric_inner_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothRiemannianMetric_inner_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothRiemannianMetric_inner_self_nonneg

lemma SmoothScalar.integral_inner_grad_self_nonneg
    {g : SmoothRiemannianMetric I M} (f : SmoothScalar g) :
    0 ≤ ∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  refine _root_.MeasureTheory.integral_nonneg ?_
  intro x
  exact SmoothRiemannianMetric_inner_self_nonneg g x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_inner_grad_self_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_inner_grad_self_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_inner_grad_self_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.integral_inner_grad_self_nonneg

lemma smoothScalarH1Inner_nonneg {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) :
    0 ≤ smoothScalarH1Inner (I := I) (M := M) f f := by
  unfold smoothScalarH1Inner
  exact add_nonneg f.integral_mul_self_nonneg f.integral_inner_grad_self_nonneg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_nonneg ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_nonneg

omit [I.Boundaryless] in
lemma smoothScalar_integral_mul_add_left {g : SmoothRiemannianMetric I M}
    (f₁ f₂ h : SmoothScalar g) :
    (∫ x, (f₁ + f₂).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, f₁.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, f₂.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : ∀ x : M, (f₁ + f₂).toFun x * h.toFun x =
      f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x := by
    intro x
    rw [SmoothScalar.toFun_add_apply]
    ring
  rw [show (fun x : M => (f₁ + f₂).toFun x * h.toFun x) =
      (fun x : M => f₁.toFun x * h.toFun x + f₂.toFun x * h.toFun x) from
      funext hpt]
  exact _root_.MeasureTheory.integral_add (f₁.integrable_mul h) (f₂.integrable_mul h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_add_left

omit [T2Space M] [CompactSpace M] in
lemma SmoothScalar.grad_g_add_apply {g : SmoothRiemannianMetric I M}
    (f₁ f₂ : SmoothScalar g) (x : M) :
    ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  have hfun : (f₁ + f₂).toFun = f₁.toFun + f₂.toFun := rfl
  change gradFun (I := I) g (f₁ + f₂).toFun x =
    gradFun (I := I) g f₁.toFun x + gradFun (I := I) g f₂.toFun x
  rw [hfun]
  exact gradFun_add (I := I) g (f₁.smooth.mdifferentiable (by simp) x)
    (f₂.smooth.mdifferentiable (by simp) x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_add_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_add_apply

lemma smoothScalar_integral_inner_grad_add_left
    {g : SmoothRiemannianMetric I M}
    (f₁ f₂ h : SmoothScalar g) :
    (∫ x, g.inner x ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, g.inner x ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
      (∫ x, g.inner x ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : ∀ x : M, g.inner x
      ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x
        ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      g.inner x
        ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    rw [SmoothScalar.grad_g_add_apply f₁ ⟨f₂.toFun, f₂.smooth⟩ x]
    rw [map_add, add_apply]
  rw [show (fun x : M => g.inner x
      ((gradG (I := I) g ⟨(f₁ + f₂).toFun, (f₁ + f₂).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        ((gradG (I := I) g ⟨f₁.toFun, f₁.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) +
      g.inner x
        ((gradG (I := I) g ⟨f₂.toFun, f₂.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) from funext hpt]
  exact _root_.MeasureTheory.integral_add (f₁.integrable_inner_grad h) (f₂.integrable_inner_grad h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_add_left

lemma smoothScalarH1Inner_add_left {g : SmoothRiemannianMetric I M}
    (f₁ f₂ h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) (f₁ + f₂) h =
      smoothScalarH1Inner (I := I) (M := M) f₁ h +
      smoothScalarH1Inner (I := I) (M := M) f₂ h := by
  unfold smoothScalarH1Inner
  rw [smoothScalar_integral_mul_add_left, smoothScalar_integral_inner_grad_add_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_add_left ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_add_left

omit [T2Space M] [CompactSpace M] in
lemma SmoothScalar.grad_g_smul_apply {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f : SmoothScalar g) (x : M) :
    ((gradG (I := I) g ⟨(c • f).toFun, (c • f).smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      c • ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  change gradFun (I := I) g (c • f).toFun x =
    c • gradFun (I := I) g f.toFun x
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradFun (I := I) g (c • f.toFun) x) v =
    g.inner x (c • gradFun (I := I) g f.toFun x) v
  rw [inner_gradFun (I := I) g (c • f.toFun) x v]
  rw [show g.inner x (c • gradFun (I := I) g f.toFun x) v =
      c * g.inner x (gradFun (I := I) g f.toFun x) v from ?_]
  swap
  · rw [map_smul, smul_apply, smul_eq_mul]
  rw [inner_gradFun (I := I) g f.toFun x v]
  set d_f : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f.toFun x with hd_f_def
  have hHaf : HasMFDerivAt I 𝓘(ℝ, ℝ) f.toFun x d_f := by
    rw [hd_f_def]
    exact (f.smooth.mdifferentiable (by simp) x).hasMFDerivAt
  have hHa_smul : HasMFDerivAt I 𝓘(ℝ, ℝ) (c • f.toFun) x (c • d_f) :=
    hHaf.const_smul c
  have hd_smul : mfderiv I 𝓘(ℝ, ℝ) (c • f.toFun) x = c • d_f :=
    hHa_smul.mfderiv
  rw [hd_smul]
  change (c • d_f) v = c * d_f v
  rw [smul_apply, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_smul_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.grad_g_smul_apply

omit [I.Boundaryless] in
lemma smoothScalar_integral_mul_smul_left {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f h : SmoothScalar g) :
    (∫ x, (c • f).toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      c * (∫ x, f.toFun x * h.toFun x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : (fun x : M => (c • f).toFun x * h.toFun x) =
      (fun x : M => c * (f.toFun x * h.toFun x)) := by
    funext x; rw [SmoothScalar.toFun_smul_apply]; ring
  rw [hpt]
  rw [_root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_mul_smul_left

lemma smoothScalar_integral_inner_grad_smul_left
    {g : SmoothRiemannianMetric I M} (c : ℝ) (f h : SmoothScalar g) :
    (∫ x, g.inner x ((gradG (I := I) g ⟨(c • f).toFun, (c • f).smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      c * (∫ x, g.inner x ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hpt : (fun x : M => g.inner x
      ((gradG (I := I) g ⟨(c • f).toFun, (c • f).smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => c * g.inner x
        ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨h.toFun, h.smooth⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
    funext x
    rw [SmoothScalar.grad_g_smul_apply c f x]
    rw [map_smul, smul_apply, smul_eq_mul]
  rw [hpt, _root_.MeasureTheory.integral_const_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalar_integral_inner_grad_smul_left

lemma smoothScalarH1Inner_smul_left {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f h : SmoothScalar g) :
    smoothScalarH1Inner (I := I) (M := M) (c • f) h =
      c * smoothScalarH1Inner (I := I) (M := M) f h := by
  unfold smoothScalarH1Inner
  rw [smoothScalar_integral_mul_smul_left, smoothScalar_integral_inner_grad_smul_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_smul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_smul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_smul_left ``Submission.DifferentialGeometry.Analysis.Laplacian.smoothScalarH1Inner_smul_left

noncomputable instance instPreInnerProductSpaceCoreSmoothScalar
    {g : SmoothRiemannianMetric I M} :
    PreInnerProductSpace.Core ℝ (SmoothScalar g) where
  inner f h := smoothScalarH1Inner (I := I) (M := M) f h
  conj_inner_symm f h := by
    change (smoothScalarH1Inner (I := I) (M := M) h f : ℝ) =
      smoothScalarH1Inner (I := I) (M := M) f h
    exact smoothScalarH1Inner_symm h f
  re_inner_nonneg f := by
    change (0 : ℝ) ≤ smoothScalarH1Inner (I := I) (M := M) f f
    exact smoothScalarH1Inner_nonneg f
  add_left f₁ f₂ h := by
    change smoothScalarH1Inner (I := I) (M := M) (f₁ + f₂) h =
      smoothScalarH1Inner (I := I) (M := M) f₁ h +
      smoothScalarH1Inner (I := I) (M := M) f₂ h
    exact smoothScalarH1Inner_add_left f₁ f₂ h
  smul_left f h c := by
    change smoothScalarH1Inner (I := I) (M := M) (c • f) h =
      c * smoothScalarH1Inner (I := I) (M := M) f h
    exact smoothScalarH1Inner_smul_left c f h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.instPreInnerProductSpaceCoreSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.instPreInnerProductSpaceCoreSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.instPreInnerProductSpaceCoreSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.instPreInnerProductSpaceCoreSmoothScalar

noncomputable instance instSeminormedAddCommGroupSmoothScalar
    {g : SmoothRiemannianMetric I M} :
    SeminormedAddCommGroup (SmoothScalar g) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.instSeminormedAddCommGroupSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.instSeminormedAddCommGroupSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.instSeminormedAddCommGroupSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.instSeminormedAddCommGroupSmoothScalar

noncomputable instance instInnerProductSpaceSmoothScalar
    {g : SmoothRiemannianMetric I M} :
    InnerProductSpace ℝ (SmoothScalar g) :=
  InnerProductSpace.ofCore _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.instInnerProductSpaceSmoothScalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.instInnerProductSpaceSmoothScalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.instInnerProductSpaceSmoothScalar ``Submission.DifferentialGeometry.Analysis.Laplacian.instInnerProductSpaceSmoothScalar

@[simp] lemma SmoothScalar.inner_def {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    @_root_.Inner.inner ℝ _ _ f h = smoothScalarH1Inner (I := I) (M := M) f h := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_def ``Submission.DifferentialGeometry.Analysis.Laplacian.SmoothScalar.inner_def

end Laplacian
end Analysis
end DifferentialGeometry

end
