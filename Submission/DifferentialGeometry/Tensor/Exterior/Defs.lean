/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
import Submission.DifferentialGeometry.Tensor.Alternating.Bundle.Defs
import Submission.DifferentialGeometry.Tensor.Alternating.Wedge
import Submission.DifferentialGeometry.Tensor.Exterior.Model
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.ContinuousAlternatingMap _root_.Submission.ContinuousAlternatingMap _root_.Bundle.ContinuousAlternatingMap _root_.Function _root_.Filter
open scoped _root_.Topology _root_.Manifold _root_.ContDiff _root_.Bundle _root_.Submission.Bundle

namespace DifferentialGeometry

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]

abbrev DifferentialForm (k : ℕ) :=
  ContMDiffSection IM (EM [⋀^Fin k]→L[ℝ] ℝ) ∞
    (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm ``Submission.DifferentialGeometry.DifferentialForm

namespace DifferentialForm

variable {IM M k}

private lemma contMDiff_add_section {s t : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x}
    (hs : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x)))
    (ht : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (t x))) :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x + t x)) := by
  intro x₀
  let e := _root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  have hs' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun x => (e ⟨x, s x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp
      (hs x₀)
  have ht' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun x => (e ⟨x, t x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp
      (ht x₀)
  refine (hs'.add ht').congr_of_eventuallyEq ?_
  exact _root_.Filter.eventually_of_mem (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt (EM
    [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_add (s x) (t x))

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.contMDiff_add_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.contMDiff_add_section target :: scope.openDecls } }

private lemma contMDiff_smul_section (c : ℝ) {s : (x : M) →
    Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x}
    (hs : ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (s x))) :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (c • s x)) := by
  intro x₀
  let e := _root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  have hs' : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun x => (e ⟨x, s x⟩).2) x₀ := by
    exact (Bundle.Trivialization.contMDiffAt_section_iff e
      (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)).mp
      (hs x₀)
  refine ((contMDiffAt_const : ContMDiffAt IM 𝓘(ℝ,
    ℝ) ∞ (fun _ : M => c) x₀).smul hs').congr_of_eventuallyEq ?_
  exact _root_.Filter.eventually_of_mem (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt (EM
    [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_smul c (s x))

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.contMDiff_smul_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.contMDiff_smul_section target :: scope.openDecls } }

private lemma contMDiff_zero_section :
    ContMDiff IM (IM.prod 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EM [⋀^Fin k]→L[ℝ] ℝ) x (0 : Bundle.continuousAlternatingMap ℝ
        (Fin k) EM
        (TangentSpace IM) ℝ (Bundle.Trivial M ℝ) x)) := by
  intro x₀
  let e := _root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀
  rw [Bundle.Trivialization.contMDiffAt_section_iff e
    (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀)]
  refine (contMDiffAt_const (c := (0 : EM [⋀^Fin k]→L[ℝ] ℝ))).congr_of_eventuallyEq ?_
  exact _root_.Filter.eventually_of_mem (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt (EM
    [⋀^Fin k]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ (Bundle.Trivial M ℝ)) x₀))
    (fun x hx => (e.linear ℝ hx).map_zero)

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.contMDiff_zero_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.contMDiff_zero_section target :: scope.openDecls } }

instance instZero : Zero (DifferentialForm IM M k) :=
  ⟨⟨fun _ => 0, contMDiff_zero_section (IM := IM) (M := M) (k := k)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instZero ``Submission.DifferentialGeometry.DifferentialForm.instZero

instance instAdd : Add (DifferentialForm IM M k) :=
  ⟨fun α β => ⟨fun x => α x + β x,
    contMDiff_add_section (IM := IM) (M := M) (k := k) α.contMDiff_toFun β.contMDiff_toFun⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instAdd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instAdd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instAdd ``Submission.DifferentialGeometry.DifferentialForm.instAdd

instance instNeg : Neg (DifferentialForm IM M k) :=
  ⟨fun α => ⟨fun x => (-1 : ℝ) • α x,
    contMDiff_smul_section (IM := IM) (M := M) (k := k) (-1 : ℝ) α.contMDiff_toFun⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instNeg ``Submission.DifferentialGeometry.DifferentialForm.instNeg

instance instSub : Sub (DifferentialForm IM M k) :=
  ⟨fun α β => ⟨fun x => α x + (-1 : ℝ) • β x,
    contMDiff_add_section (IM := IM) (M := M) (k := k) α.contMDiff_toFun
      (contMDiff_smul_section (IM := IM) (M := M) (k := k) (-1 : ℝ) β.contMDiff_toFun)⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instSub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instSub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instSub ``Submission.DifferentialGeometry.DifferentialForm.instSub

instance instSMul : SMul ℝ (DifferentialForm IM M k) :=
  ⟨fun c α => ⟨fun x => c • α x,
    contMDiff_smul_section (IM := IM) (M := M) (k := k) c α.contMDiff_toFun⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instSMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instSMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instSMul ``Submission.DifferentialGeometry.DifferentialForm.instSMul

@[simp] theorem zero_apply (x : M) : (0 : DifferentialForm IM M k) x = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.zero_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.zero_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.zero_apply ``Submission.DifferentialGeometry.DifferentialForm.zero_apply
@[simp] theorem add_apply (α β : DifferentialForm IM M k) (x : M) : (α + β) x = α x + β x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.add_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.add_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.add_apply ``Submission.DifferentialGeometry.DifferentialForm.add_apply
@[simp] theorem neg_apply (α : DifferentialForm IM M k) (x : M) : (-α) x = (-1 : ℝ) • α x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.neg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.neg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.neg_apply ``Submission.DifferentialGeometry.DifferentialForm.neg_apply
@[simp] theorem sub_apply (α β : DifferentialForm IM M k) (x : M) : (α - β) x = α x +
    (-1 : ℝ) • β x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.sub_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.sub_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.sub_apply ``Submission.DifferentialGeometry.DifferentialForm.sub_apply
@[simp] theorem smul_apply (c : ℝ) (α : DifferentialForm IM M k) (x : M) :
    (c • α) x = c • α x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.smul_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.smul_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.smul_apply ``Submission.DifferentialGeometry.DifferentialForm.smul_apply

instance instAddCommGroup : AddCommGroup (DifferentialForm IM M k) :=
  { zero := 0
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := by intro a b c; apply ContMDiffSection.ext; intro x; simp [add_assoc]
    zero_add := by intro a; apply ContMDiffSection.ext; intro x; simp
    add_zero := by intro a; apply ContMDiffSection.ext; intro x; simp
    add_comm := by intro a b; apply ContMDiffSection.ext; intro x; simp [add_comm]
    neg_add_cancel := by
      intro a
      apply ContMDiffSection.ext
      intro x
      simp only [add_apply, neg_apply, zero_apply]
      nth_rw 2 [show a x = (1 : ℝ) • a x from (one_smul ℝ (a x)).symm]
      rw [← add_smul]
      norm_num
    sub_eq_add_neg := by intro a b; apply ContMDiffSection.ext; intro x; rfl
    }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instAddCommGroup ``Submission.DifferentialGeometry.DifferentialForm.instAddCommGroup

instance instModule : Module ℝ (DifferentialForm IM M k) :=
  { smul := (· • ·)
    smul_zero := by intro c; apply ContMDiffSection.ext; intro x; simp
    zero_smul := by intro a; apply ContMDiffSection.ext; intro x; simp
    smul_add := by intro c a b; apply ContMDiffSection.ext; intro x; simp [smul_add]
    add_smul := by intro c d a; apply ContMDiffSection.ext; intro x; simp [add_smul]
    mul_smul := by intro c d a; apply ContMDiffSection.ext; intro x; simp [_root_.SemigroupAction.mul_smul]
    one_smul := by intro a; apply ContMDiffSection.ext; intro x; simp }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.instModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.instModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.instModule ``Submission.DifferentialGeometry.DifferentialForm.instModule

noncomputable def wedge {k l : ℕ} (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) : DifferentialForm IM M (k + l) :=
  ⟨fun x => ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ), by
    intro x₀
    let e := _root_.FiberBundle.trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e
      (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hα : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun x =>
        (_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (α.contMDiff_toFun x₀)
    have hβ : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin l]→L[ℝ] ℝ) ∞ (fun x =>
        (_root_.FiberBundle.trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, β x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (_root_.FiberBundle.trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀)).mp (β.contMDiff_toFun x₀)
    let dNorm : NormedAddCommGroup ((EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := EM [⋀^Fin l]→L[ℝ] ℝ) (F := EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (σ₁₂ := RingHom.id ℝ)
    let dSpace : NormedSpace ℝ ((EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ]
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := EM [⋀^Fin l]→L[ℝ] ℝ) (F := EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (σ₁₂ := RingHom.id ℝ)
    let oNorm : NormedAddCommGroup ((EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ((EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin (k + l)]→L[ℝ] ℝ))) :=
      ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := EM [⋀^Fin k]→L[ℝ] ℝ)
        (F := (EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin (k + l)]→L[ℝ] ℝ))
        (σ₁₂ := RingHom.id ℝ)
    let oSpace : NormedSpace ℝ ((EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ((EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin (k + l)]→L[ℝ] ℝ))) :=
      ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ)
        (E := EM [⋀^Fin k]→L[ℝ] ℝ)
        (F := (EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin (k + l)]→L[ℝ] ℝ))
        (σ₁₂ := RingHom.id ℝ)
    let W : (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ((EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)) :=
      wedgeProductL (M := EM) (m := k) (n := l) (ContinuousLinearMap.mul ℝ ℝ)
    have hW : ContMDiffAt IM 𝓘(ℝ, (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ]
        ((EM [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin (k + l)]→L[ℝ] ℝ))) ∞ (fun _ : M => W) x₀ :=
      contMDiffAt_const
    refine ((hW.clm_apply hα).clm_apply hβ).congr_of_eventuallyEq ?_
    exact _root_.Filter.eventually_of_mem (e.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt
        (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀))
      (fun x hx => by
        change ((_root_.FiberBundle.trivializationAt (EM [⋀^Fin (k + l)]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin (k + l)) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀)
            ⟨x, ContinuousAlternatingMap.wedgeProduct (α x) (β x)
              (ContinuousLinearMap.mul ℝ ℝ)⟩).2 =
          W ((_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀) ⟨x, α x⟩).2
            ((_root_.FiberBundle.trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
              (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
                (Bundle.Trivial M ℝ)) x₀) ⟨x, β x⟩).2
        rw [continuousAlternatingMap_trivializationAt_apply (m := k + l) (IM := IM) (M := M)
          (x₀ := x₀) (x := x)
          (L := ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)),
          continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M)
            (x₀ := x₀) (x := x) (L := α x),
          continuousAlternatingMap_trivializationAt_apply (m := l) (IM := IM) (M := M)
            (x₀ := x₀) (x := x) (L := β x)]
        rw [show W ((α x).compContinuousLinearMap ((_root_.FiberBundle.trivializationAt EM
          (TangentSpace IM) x₀).symmL ℝ x))
              ((β x).compContinuousLinearMap ((_root_.FiberBundle.trivializationAt EM
                (TangentSpace IM) x₀).symmL ℝ x)) =
              ContinuousAlternatingMap.wedgeProduct ((α x).compContinuousLinearMap
                ((_root_.FiberBundle.trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
                ((β x).compContinuousLinearMap ((_root_.FiberBundle.trivializationAt EM
                  (TangentSpace IM) x₀).symmL ℝ x))
                (ContinuousLinearMap.mul ℝ ℝ) from by
          simp [W, wedge_productL_apply]]
        exact (DifferentialGeometry.DifferentialForm.wedge_product_compContinuousLinearMap
          (E := TangentSpace IM x) (E' := TangentSpace IM x)
          (g := α x) (h := β x) (A := (_root_.FiberBundle.trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge ``Submission.DifferentialGeometry.DifferentialForm.wedge

private def domDomCongrL {k l : ℕ} (e : Fin k ≃ Fin l) :
    (EM [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] (EM [⋀^Fin l]→L[ℝ] ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousAlternatingMap.domDomCongr e f
      map_add' := fun f g => ContinuousAlternatingMap.domDomCongr_add e f g
      map_smul' := fun c f => by
        ext v
        simp [ContinuousAlternatingMap.domDomCongr_apply] }
    1 (fun f => by
      have hnorm : ‖ContinuousAlternatingMap.domDomCongr e f‖ = ‖f‖ := by
        change ‖(ContinuousAlternatingMap.domDomCongr e f).toContinuousMultilinearMap‖ = ‖f‖
        change ‖(f.toContinuousMultilinearMap.domDomCongr e : ContinuousMultilinearMap ℝ
          (fun _ : Fin l => EM) ℝ)‖ = ‖f‖
        rw [ContinuousMultilinearMap.norm_domDomCongr]
        rw [ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      simp [hnorm])

run_cmd do
  let target := ``Submission.DifferentialGeometry.DifferentialForm.domDomCongrL
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.DifferentialForm.domDomCongrL target :: scope.openDecls } }

noncomputable def reindex {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M k) :
    DifferentialForm IM M l :=
  ⟨fun x => ContinuousAlternatingMap.domDomCongr e (α x), by
    intro x₀
    let e' := _root_.FiberBundle.trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀
    rw [Bundle.Trivialization.contMDiffAt_section_iff e'
      (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
        (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
          (Bundle.Trivial M ℝ)) x₀)]
    have hα : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin k]→L[ℝ] ℝ) ∞ (fun x =>
        (_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2) x₀ := by
      exact (Bundle.Trivialization.contMDiffAt_section_iff
        (_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)
        (_root_.FiberBundle.mem_baseSet_trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀)).mp (α.contMDiff_toFun x₀)
    have hL : ContMDiffAt IM 𝓘(ℝ, EM [⋀^Fin l]→L[ℝ] ℝ) ∞ (fun x =>
        (domDomCongrL e) ((_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
          (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
            (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2)) x₀ := by
      exact (contMDiffAt_const (c := domDomCongrL e)).clm_apply hα
    refine hL.congr_of_eventuallyEq ?_
    exact _root_.Filter.eventually_of_mem (e'.open_baseSet.mem_nhds (_root_.FiberBundle.mem_baseSet_trivializationAt
      (EM [⋀^Fin l]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀))
      (fun x hx => by
        change (_root_.FiberBundle.trivializationAt (EM [⋀^Fin l]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin l) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀
            ⟨x, ContinuousAlternatingMap.domDomCongr e (α x)⟩).2 =
          (domDomCongrL e) ((_root_.FiberBundle.trivializationAt (EM [⋀^Fin k]→L[ℝ] ℝ)
            (Bundle.continuousAlternatingMap ℝ (Fin k) EM (TangentSpace IM) ℝ
              (Bundle.Trivial M ℝ)) x₀ ⟨x, α x⟩).2)
        rw [continuousAlternatingMap_trivializationAt_apply (m := l) (IM := IM) (M := M)
          (x₀ := x₀) (x := x)
          (L := ContinuousAlternatingMap.domDomCongr e (α x)),
          continuousAlternatingMap_trivializationAt_apply (m := k) (IM := IM) (M := M)
            (x₀ := x₀) (x := x) (L := α x)]
        change (ContinuousAlternatingMap.domDomCongr e (α x)).compContinuousLinearMap
            ((_root_.FiberBundle.trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x) =
          ContinuousAlternatingMap.domDomCongr e ((α x).compContinuousLinearMap
            ((_root_.FiberBundle.trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x))
        exact (domDomCongr_compContinuousLinearMap
          (E := TangentSpace IM x) (E' := TangentSpace IM x) (σ := e)
          (L := α x) (A := (_root_.FiberBundle.trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x)).symm)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.reindex ``Submission.DifferentialGeometry.DifferentialForm.reindex

@[simp] theorem reindex_apply {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M k) (x : M) :
    (reindex e α) x = ContinuousAlternatingMap.domDomCongr e (α x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.reindex_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.reindex_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.reindex_apply ``Submission.DifferentialGeometry.DifferentialForm.reindex_apply

@[simp] theorem reindex_refl (α : DifferentialForm IM M k) :
    reindex (Equiv.refl (Fin k)) α = α := by
  apply ContMDiffSection.ext
  intro x
  simp [reindex_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.reindex_refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.reindex_refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.reindex_refl ``Submission.DifferentialGeometry.DifferentialForm.reindex_refl

theorem reindex_comp {k l m : ℕ} (e : Fin k ≃ Fin l) (f : Fin l ≃ Fin m)
    (α : DifferentialForm IM M k) :
    reindex f (reindex e α) = reindex (e.trans f) α := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.domDomCongr f (ContinuousAlternatingMap.domDomCongr e (α x)) =
    ContinuousAlternatingMap.domDomCongr (e.trans f) (α x)
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.reindex_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.reindex_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.reindex_comp ``Submission.DifferentialGeometry.DifferentialForm.reindex_comp

@[simp] theorem reindex_reindex_symm
    {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M l) :
    reindex e (reindex e.symm α) = α := by
  rw [reindex_comp e.symm e α, Equiv.symm_trans_self, reindex_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.reindex_reindex_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.reindex_reindex_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.reindex_reindex_symm ``Submission.DifferentialGeometry.DifferentialForm.reindex_reindex_symm

@[simp] theorem reindex_symm_reindex
    {k l : ℕ} (e : Fin k ≃ Fin l) (α : DifferentialForm IM M k) :
    reindex e.symm (reindex e α) = α := by
  rw [reindex_comp e e.symm α, Equiv.self_trans_symm, reindex_refl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.reindex_symm_reindex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.reindex_symm_reindex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.reindex_symm_reindex ``Submission.DifferentialGeometry.DifferentialForm.reindex_symm_reindex

scoped notation:70 α " ∧ " β => DifferentialForm.wedge α β

theorem add_wedge {k l : ℕ} (α β : DifferentialForm IM M k)
    (γ : DifferentialForm IM M l) :
    DifferentialForm.wedge (α + β) γ = DifferentialForm.wedge α γ + DifferentialForm.wedge β γ := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.wedgeProduct (α x + β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ) =
    ContinuousAlternatingMap.wedgeProduct (α x) (γ x) (ContinuousLinearMap.mul ℝ ℝ) +
    ContinuousAlternatingMap.wedgeProduct (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.add_wedge (α x) (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.add_wedge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.add_wedge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.add_wedge ``Submission.DifferentialGeometry.DifferentialForm.add_wedge

theorem wedge_add {k l : ℕ} (α : DifferentialForm IM M k)
    (β γ : DifferentialForm IM M l) :
    DifferentialForm.wedge α (β + γ) = DifferentialForm.wedge α β + DifferentialForm.wedge α γ := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.wedgeProduct (α x) (β x + γ x) (ContinuousLinearMap.mul ℝ ℝ) =
    ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ) +
    ContinuousAlternatingMap.wedgeProduct (α x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.wedge_add (α x) (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge_add ``Submission.DifferentialGeometry.DifferentialForm.wedge_add

theorem smul_wedge {k l : ℕ} (c : ℝ) (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) :
    DifferentialForm.wedge (c • α) β = c • DifferentialForm.wedge α β := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.wedgeProduct (c • α x) (β x) (ContinuousLinearMap.mul ℝ ℝ) =
    c • ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.smul_wedge c (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.smul_wedge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.smul_wedge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.smul_wedge ``Submission.DifferentialGeometry.DifferentialForm.smul_wedge

theorem wedge_smul {k l : ℕ} (c : ℝ) (α : DifferentialForm IM M k)
    (β : DifferentialForm IM M l) :
    DifferentialForm.wedge α (c • β) = c • DifferentialForm.wedge α β := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.wedgeProduct (α x) (c • β x) (ContinuousLinearMap.mul ℝ ℝ) =
    c • ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.wedge_smul c (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge_smul ``Submission.DifferentialGeometry.DifferentialForm.wedge_smul

theorem wedge_comm {k l : ℕ} (α : DifferentialForm IM M k) (β : DifferentialForm IM M l) :
    DifferentialForm.wedge α β = reindex (Fin.finAddCongr (m := l) (n := k))
      ((-1 : ℝ)^(k*l) • DifferentialForm.wedge β α) := by
  apply ContMDiffSection.ext
  intro x
  simp only [DifferentialForm.wedge, reindex_apply, smul_apply]
  exact ContinuousAlternatingMap.wedge_antisymm (𝕜 := ℝ) (M := TangentSpace IM x)
    (m := k) (n := l) (α x) (β x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge_comm ``Submission.DifferentialGeometry.DifferentialForm.wedge_comm

theorem wedge_self_odd_zero {k : ℕ} (α : DifferentialForm IM M k) (hk : Odd k) :
    DifferentialForm.wedge α α = 0 := by
  apply ContMDiffSection.ext
  intro x
  exact ContinuousAlternatingMap.wedge_self_odd_zero (M := TangentSpace IM x) (m := k)
    (α x) hk (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge_self_odd_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge_self_odd_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge_self_odd_zero ``Submission.DifferentialGeometry.DifferentialForm.wedge_self_odd_zero

theorem wedge_assoc {k l r : ℕ} (α : DifferentialForm IM M k) (β : DifferentialForm IM M l)
    (γ : DifferentialForm IM M r) :
    reindex Fin.finAssoc.symm (DifferentialForm.wedge α (DifferentialForm.wedge β γ)) =
      DifferentialForm.wedge (DifferentialForm.wedge α β) γ := by
  apply ContMDiffSection.ext
  intro x
  change ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
      (ContinuousAlternatingMap.wedgeProduct (α x)
        (ContinuousAlternatingMap.wedgeProduct (β x) (γ x) (ContinuousLinearMap.mul ℝ ℝ))
        (ContinuousLinearMap.mul ℝ ℝ)) =
    ContinuousAlternatingMap.wedgeProduct
      (ContinuousAlternatingMap.wedgeProduct (α x) (β x) (ContinuousLinearMap.mul ℝ ℝ))
      (γ x) (ContinuousLinearMap.mul ℝ ℝ)
  exact ContinuousAlternatingMap.wedge_mul_assoc (M := TangentSpace IM x) (m := k) (n := l)
    (p := r) (α x) (β x) (γ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.DifferentialForm.wedge_assoc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.DifferentialForm.wedge_assoc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.DifferentialForm.wedge_assoc ``Submission.DifferentialGeometry.DifferentialForm.wedge_assoc

end DifferentialForm

end DifferentialGeometry

end
