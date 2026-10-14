/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.ULift
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

universe u v

namespace DifferentialGeometry.Algebra.Group

theorem coprodI_subsingleton_iff {ι : Type u} (G : ι → Type v) [∀ i, Group (G i)] :
    Subsingleton (Monoid.CoprodI G) ↔ ∀ i, Subsingleton (G i) := by
  constructor
  · intro h i
    constructor
    intro x y
    apply Monoid.CoprodI.of_injective i
    exact h.elim _ _
  · intro h
    constructor
    intro x y
    suffices all_eq_one : ∀ z : Monoid.CoprodI G, z = 1 by
      exact (all_eq_one x).trans (all_eq_one y).symm
    intro z
    induction z using Monoid.CoprodI.induction_on with
    | one => rfl
    | of i g =>
        have hg : g = 1 := (h i).elim _ _
        simp [hg]
    | mul x y hx hy => simp [hx, hy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff ``Submission.DifferentialGeometry.Algebra.Group.coprodI_subsingleton_iff

universe w x

def coprodIMap {ι : Type u}
    (G : ι → Type v) (H : ι → Type w)
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (f : ∀ i, G i →* H i) : Monoid.CoprodI G →* Monoid.CoprodI H :=
  Monoid.CoprodI.lift fun i ↦
    (Monoid.CoprodI.of : H i →* Monoid.CoprodI H).comp (f i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIMap ``Submission.DifferentialGeometry.Algebra.Group.coprodIMap

@[simp]
theorem coprodIMap_comp_of {ι : Type u}
    (G : ι → Type v) (H : ι → Type w)
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (f : ∀ i, G i →* H i) (i : ι) :
    (coprodIMap G H f).comp (Monoid.CoprodI.of : G i →* Monoid.CoprodI G) =
      (Monoid.CoprodI.of : H i →* Monoid.CoprodI H).comp (f i) := by
  exact Monoid.CoprodI.lift_comp_of _ i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIMap_comp_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIMap_comp_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIMap_comp_of ``Submission.DifferentialGeometry.Algebra.Group.coprodIMap_comp_of

@[simp]
theorem coprodIMap_of {ι : Type u}
    (G : ι → Type v) (H : ι → Type w)
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (f : ∀ i, G i →* H i) (i : ι) (g : G i) :
    coprodIMap G H f (Monoid.CoprodI.of g) = Monoid.CoprodI.of (f i g) := by
  rw [← MonoidHom.comp_apply, coprodIMap_comp_of]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIMap_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIMap_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIMap_of ``Submission.DifferentialGeometry.Algebra.Group.coprodIMap_of

def coprodIMulEquiv {ι : Type u}
    (G : ι → Type v) (H : ι → Type w)
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) : Monoid.CoprodI G ≃* Monoid.CoprodI H :=
  MonoidHom.toMulEquiv
    (coprodIMap G H fun i ↦ (e i).toMonoidHom)
    (coprodIMap H G fun i ↦ (e i).symm.toMonoidHom)
    (by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext g
      simp)
    (by
      apply Monoid.CoprodI.ext_hom
      intro i
      ext h
      simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIMulEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIMulEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIMulEquiv ``Submission.DifferentialGeometry.Algebra.Group.coprodIMulEquiv

@[simp]
theorem coprodIMulEquiv_comp_of {ι : Type u}
    (G : ι → Type v) (H : ι → Type w)
    [∀ i, Group (G i)] [∀ i, Group (H i)]
    (e : ∀ i, G i ≃* H i) (i : ι) :
    (↑(coprodIMulEquiv G H e) : Monoid.CoprodI G →* Monoid.CoprodI H).comp
        (Monoid.CoprodI.of : G i →* Monoid.CoprodI G) =
      (Monoid.CoprodI.of : H i →* Monoid.CoprodI H).comp (e i).toMonoidHom := by
  exact coprodIMap_comp_of G H (fun i ↦ (e i).toMonoidHom) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIMulEquiv_comp_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIMulEquiv_comp_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIMulEquiv_comp_of ``Submission.DifferentialGeometry.Algebra.Group.coprodIMulEquiv_comp_of

noncomputable def coprodIReindexEquiv
    {ι : Type u} {κ : Type v} (G : ι → Type w) (H : κ → Type x)
    [∀ i, Group (G i)] [∀ j, Group (H j)]
    (e : ι ≃ κ) (f : ∀ i, G i ≃* H (e i)) :
    Monoid.CoprodI G ≃* Monoid.CoprodI H := by
  let forward : Monoid.CoprodI G →* Monoid.CoprodI H :=
    Monoid.CoprodI.lift fun i ↦
      (Monoid.CoprodI.of : H (e i) →* Monoid.CoprodI H).comp
        (f i).toMonoidHom
  let inverseFactors : ∀ j, H j →* Monoid.CoprodI G :=
    Equiv.piCongrLeft (fun j ↦ H j →* Monoid.CoprodI G) e fun i ↦
      (Monoid.CoprodI.of : G i →* Monoid.CoprodI G).comp
        (f i).symm.toMonoidHom
  let inverse : Monoid.CoprodI H →* Monoid.CoprodI G :=
    Monoid.CoprodI.lift inverseFactors
  refine MonoidHom.toMulEquiv forward inverse ?_ ?_
  · apply Monoid.CoprodI.ext_hom
    intro i
    ext g
    simp [forward, inverse, inverseFactors]
  · apply Monoid.CoprodI.ext_hom
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    ext h
    simp [forward, inverse, inverseFactors]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIReindexEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIReindexEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIReindexEquiv ``Submission.DifferentialGeometry.Algebra.Group.coprodIReindexEquiv

@[simp]
theorem coprodIReindexEquiv_comp_of
    {ι : Type u} {κ : Type v} (G : ι → Type w) (H : κ → Type x)
    [∀ i, Group (G i)] [∀ j, Group (H j)]
    (e : ι ≃ κ) (f : ∀ i, G i ≃* H (e i)) (i : ι) :
    (↑(coprodIReindexEquiv G H e f) : Monoid.CoprodI G →* Monoid.CoprodI H).comp
        (Monoid.CoprodI.of : G i →* Monoid.CoprodI G) =
      (Monoid.CoprodI.of : H (e i) →* Monoid.CoprodI H).comp
        (f i).toMonoidHom := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIReindexEquiv_comp_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIReindexEquiv_comp_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIReindexEquiv_comp_of ``Submission.DifferentialGeometry.Algebra.Group.coprodIReindexEquiv_comp_of

noncomputable def coprodIEmptyEquivPUnit
    (G : Empty → Type v) [∀ i, Group (G i)] :
    Monoid.CoprodI G ≃* PUnit := by
  letI : Subsingleton (Monoid.CoprodI G) :=
    (coprodI_subsingleton_iff G).mpr fun i ↦ i.elim
  letI : Unique (Monoid.CoprodI G) :=
    { default := 1
      uniq := fun x ↦ Subsingleton.elim x 1 }
  exact MulEquiv.ofUnique

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIEmptyEquivPUnit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIEmptyEquivPUnit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIEmptyEquivPUnit ``Submission.DifferentialGeometry.Algebra.Group.coprodIEmptyEquivPUnit

def coprodISingletonToFactor (H : Type v) [Group H] :
    Monoid.CoprodI (fun _ : PUnit ↦ H) →* H :=
  Monoid.CoprodI.lift fun _ ↦ MonoidHom.id H

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodISingletonToFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodISingletonToFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodISingletonToFactor ``Submission.DifferentialGeometry.Algebra.Group.coprodISingletonToFactor

def factorToCoprodISingleton (H : Type v) [Group H] :
    H →* Monoid.CoprodI (fun _ : PUnit ↦ H) :=
  Monoid.CoprodI.of (M := fun _ : PUnit ↦ H) (i := PUnit.unit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.factorToCoprodISingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.factorToCoprodISingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.factorToCoprodISingleton ``Submission.DifferentialGeometry.Algebra.Group.factorToCoprodISingleton

theorem coprodISingletonMaps_forward_inverse (H : Type v) [Group H] :
    (coprodISingletonToFactor H).comp (factorToCoprodISingleton H) =
      MonoidHom.id H := by
  ext h
  simp [coprodISingletonToFactor, factorToCoprodISingleton]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodISingletonMaps_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodISingletonMaps_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodISingletonMaps_forward_inverse ``Submission.DifferentialGeometry.Algebra.Group.coprodISingletonMaps_forward_inverse

theorem coprodISingletonMaps_inverse_forward (H : Type v) [Group H] :
    (factorToCoprodISingleton H).comp (coprodISingletonToFactor H) =
      MonoidHom.id (Monoid.CoprodI (fun _ : PUnit ↦ H)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  rcases i with ⟨⟩
  ext h
  simp [factorToCoprodISingleton, coprodISingletonToFactor]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodISingletonMaps_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodISingletonMaps_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodISingletonMaps_inverse_forward ``Submission.DifferentialGeometry.Algebra.Group.coprodISingletonMaps_inverse_forward

def coprodISingletonEquiv (H : Type v) [Group H] :
    Monoid.CoprodI (fun _ : PUnit ↦ H) ≃* H :=
  MonoidHom.toMulEquiv
    (coprodISingletonToFactor H)
    (factorToCoprodISingleton H)
    (coprodISingletonMaps_inverse_forward H)
    (coprodISingletonMaps_forward_inverse H)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodISingletonEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodISingletonEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodISingletonEquiv ``Submission.DifferentialGeometry.Algebra.Group.coprodISingletonEquiv

@[simp]
theorem coprodISingletonEquiv_of (H : Type v) [Group H] (h : H) :
    coprodISingletonEquiv H
      (Monoid.CoprodI.of (M := fun _ : PUnit ↦ H) (i := PUnit.unit) h) = h := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodISingletonEquiv_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodISingletonEquiv_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodISingletonEquiv_of ``Submission.DifferentialGeometry.Algebra.Group.coprodISingletonEquiv_of

abbrev boolCoprodFamily (G : Type u) (H : Type v) : Bool → Type (max u v)
  | false => ULift.{v} G
  | true => ULift.{u} H

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.boolCoprodFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.boolCoprodFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.boolCoprodFamily ``Submission.DifferentialGeometry.Algebra.Group.boolCoprodFamily

instance boolCoprodFamilyGroup (G : Type u) (H : Type v) [Group G] [Group H]
    (i : Bool) : Group (boolCoprodFamily G H i) := by
  cases i <;> simp only [boolCoprodFamily] <;> infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.boolCoprodFamilyGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.boolCoprodFamilyGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.boolCoprodFamilyGroup ``Submission.DifferentialGeometry.Algebra.Group.boolCoprodFamilyGroup

def coprodIBoolToCoprod (G : Type u) (H : Type v) [Group G] [Group H] :
    Monoid.CoprodI (boolCoprodFamily G H) →* Monoid.Coprod G H :=
  Monoid.CoprodI.lift fun
    | false => Monoid.Coprod.inl.comp
        (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom
    | true => Monoid.Coprod.inr.comp
        (MulEquiv.ulift : ULift.{u} H ≃* H).toMonoidHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIBoolToCoprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIBoolToCoprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIBoolToCoprod ``Submission.DifferentialGeometry.Algebra.Group.coprodIBoolToCoprod

def coprodToCoprodIBool (G : Type u) (H : Type v) [Group G] [Group H] :
    Monoid.Coprod G H →* Monoid.CoprodI (boolCoprodFamily G H) :=
  Monoid.Coprod.lift
    ((Monoid.CoprodI.of : boolCoprodFamily G H _root_.Bool.false →*
      Monoid.CoprodI (boolCoprodFamily G H)).comp
        (MulEquiv.ulift : ULift.{v} G ≃* G).symm.toMonoidHom)
    ((Monoid.CoprodI.of : boolCoprodFamily G H _root_.Bool.true →*
      Monoid.CoprodI (boolCoprodFamily G H)).comp
        (MulEquiv.ulift : ULift.{u} H ≃* H).symm.toMonoidHom)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodToCoprodIBool then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodToCoprodIBool"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodToCoprodIBool ``Submission.DifferentialGeometry.Algebra.Group.coprodToCoprodIBool

theorem coprodIBoolMaps_forward_inverse (G : Type u) (H : Type v) [Group G] [Group H] :
    (coprodIBoolToCoprod G H).comp (coprodToCoprodIBool G H) =
      MonoidHom.id (Monoid.Coprod G H) := by
  apply Monoid.Coprod.hom_ext
  · ext g
    simp [coprodIBoolToCoprod, coprodToCoprodIBool]
  · ext h
    simp [coprodIBoolToCoprod, coprodToCoprodIBool]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIBoolMaps_forward_inverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIBoolMaps_forward_inverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIBoolMaps_forward_inverse ``Submission.DifferentialGeometry.Algebra.Group.coprodIBoolMaps_forward_inverse

theorem coprodIBoolMaps_inverse_forward (G : Type u) (H : Type v) [Group G] [Group H] :
    (coprodToCoprodIBool G H).comp (coprodIBoolToCoprod G H) =
      MonoidHom.id (Monoid.CoprodI (boolCoprodFamily G H)) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  cases i <;> ext g <;> simp [coprodIBoolToCoprod, coprodToCoprodIBool]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIBoolMaps_inverse_forward then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIBoolMaps_inverse_forward"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIBoolMaps_inverse_forward ``Submission.DifferentialGeometry.Algebra.Group.coprodIBoolMaps_inverse_forward

def coprodIBoolEquivCoprod (G : Type u) (H : Type v) [Group G] [Group H] :
    Monoid.CoprodI (boolCoprodFamily G H) ≃* Monoid.Coprod G H :=
  MonoidHom.toMulEquiv (coprodIBoolToCoprod G H) (coprodToCoprodIBool G H)
    (coprodIBoolMaps_inverse_forward G H) (coprodIBoolMaps_forward_inverse G H)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod ``Submission.DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod

theorem coprodIBoolEquivCoprod_of_false (G : Type u) (H : Type v) [Group G] [Group H]
    (g : ULift.{v} G) :
    coprodIBoolEquivCoprod G H (Monoid.CoprodI.of (i := _root_.Bool.false) g) =
      Monoid.Coprod.inl g.down := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_false ``Submission.DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_false

theorem coprodIBoolEquivCoprod_of_true (G : Type u) (H : Type v) [Group G] [Group H]
    (h : ULift.{u} H) :
    coprodIBoolEquivCoprod G H (Monoid.CoprodI.of (i := _root_.Bool.true) h) =
      Monoid.Coprod.inr h.down := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_true ``Submission.DifferentialGeometry.Algebra.Group.coprodIBoolEquivCoprod_of_true

end DifferentialGeometry.Algebra.Group
