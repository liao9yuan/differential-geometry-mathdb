/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Submission.DifferentialGeometry.Topology.VanKampen.SelectedObjects
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Category.ULift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.CategoryTheory _root_.Set

universe u v w t

namespace DifferentialGeometry.Topology.VanKampen

@[simp] theorem fullSubgroupoid_coe_id {C : Type u} [_root_.CategoryTheory.Groupoid C]
    (D : Set C) (x : (CategoryTheory.Subgroupoid.full D).objs) :
    (𝟙 x : x ⟶ x).1 = 𝟙 x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_id ``Submission.DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_id

@[simp] theorem fullSubgroupoid_coe_comp {C : Type u} [_root_.CategoryTheory.Groupoid C]
    (D : Set C) {x y z : (CategoryTheory.Subgroupoid.full D).objs}
    (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g : x ⟶ z).1 = f.1 ≫ g.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_comp ``Submission.DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_comp

theorem fullSubgroupoid_coe_eqToHom {C : Type u} [_root_.CategoryTheory.Groupoid C]
    (D : Set C) {x y : (CategoryTheory.Subgroupoid.full D).objs} (h : x = y) :
    (_root_.CategoryTheory.eqToHom h : x ⟶ y).1 = _root_.CategoryTheory.eqToHom (congrArg Subtype.val h) := by
  exact _root_.CategoryTheory.eqToHom_map (CategoryTheory.Subgroupoid.hom
    (CategoryTheory.Subgroupoid.full D)) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_eqToHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_eqToHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_eqToHom ``Submission.DifferentialGeometry.Topology.VanKampen.fullSubgroupoid_coe_eqToHom

@[instance_reducible] def uliftGroupoid (C : Type t) [Groupoid.{v} C] :
    Groupoid.{v} (ULift.{w} C) where
  toCategory := CategoryTheory.uliftCategory C
  inv f := Groupoid.inv f
  inv_comp f := Groupoid.inv_comp f
  comp_inv f := Groupoid.comp_inv f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.uliftGroupoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.uliftGroupoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.uliftGroupoid ``Submission.DifferentialGeometry.Topology.VanKampen.uliftGroupoid

def pointedSelectedObject {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) : FundamentalGroupoidOn Y A :=
  ⟨FundamentalGroupoid.mk y₀, by
    rw [CategoryTheory.Subgroupoid.mem_full_objs_iff]
    exact hy₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pointedSelectedObject then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pointedSelectedObject"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pointedSelectedObject ``Submission.DifferentialGeometry.Topology.VanKampen.pointedSelectedObject

theorem selectedObject_eq_pointed {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀)
    (z : FundamentalGroupoidOn Y A) : z = pointedSelectedObject A y₀ hy₀ := by
  apply Subtype.ext
  apply FundamentalGroupoid.ext
  change z.1.as = y₀
  exact huniq z.1.as ((CategoryTheory.Subgroupoid.mem_full_objs_iff
    {z : FundamentalGroupoid Y | z.as ∈ A}).1 z.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedObject_eq_pointed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedObject_eq_pointed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedObject_eq_pointed ``Submission.DifferentialGeometry.Topology.VanKampen.selectedObject_eq_pointed

noncomputable def pointedDeloopingFunctor {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀) :
    FundamentalGroupoidOn Y A ⥤ _root_.CategoryTheory.SingleObj (FundamentalGroup Y y₀) where
  obj _ := SingleObj.star _
  map {x y} f :=
    (_root_.CategoryTheory.eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq x).symm ≫ f ≫
      _root_.CategoryTheory.eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq y)).1
  map_id x := by
    have hx := selectedObject_eq_pointed A y₀ hy₀ huniq x
    subst x
    simp
    rfl
  map_comp {x y z} f g := by
    have hx := selectedObject_eq_pointed A y₀ hy₀ huniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ huniq y
    have hz := selectedObject_eq_pointed A y₀ hy₀ huniq z
    subst x
    subst y
    subst z
    simp
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pointedDeloopingFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pointedDeloopingFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pointedDeloopingFunctor ``Submission.DifferentialGeometry.Topology.VanKampen.pointedDeloopingFunctor

noncomputable def pointedDeloopingInverse {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) :
    _root_.CategoryTheory.SingleObj (FundamentalGroup Y y₀) ⥤ FundamentalGroupoidOn Y A where
  obj _ := pointedSelectedObject A y₀ hy₀
  map f := ⟨f, by
    apply (CategoryTheory.Subgroupoid.mem_full_iff _).2
    constructor <;> exact hy₀⟩
  map_id _ := by
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply Subtype.ext
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pointedDeloopingInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pointedDeloopingInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pointedDeloopingInverse ``Submission.DifferentialGeometry.Topology.VanKampen.pointedDeloopingInverse

theorem pointedDelooping_inv_hom_id {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀) :
    pointedDeloopingInverse A y₀ hy₀ ⋙ pointedDeloopingFunctor A y₀ hy₀ huniq =
      𝟭 (_root_.CategoryTheory.SingleObj (FundamentalGroup Y y₀)) := by
  apply Functor.hext
  · intro z
    exact Subsingleton.elim _ _
  · intro x y f
    have hx : x = SingleObj.star _ := Subsingleton.elim _ _
    have hy : y = SingleObj.star _ := Subsingleton.elim _ _
    subst x
    subst y
    apply heq_of_eq
    change
      (_root_.CategoryTheory.eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq
          (pointedSelectedObject A y₀ hy₀)).symm ≫
        (⟨f, by
          apply (CategoryTheory.Subgroupoid.mem_full_iff _).2
          constructor <;> exact hy₀⟩ :
            pointedSelectedObject A y₀ hy₀ ⟶ pointedSelectedObject A y₀ hy₀) ≫
        _root_.CategoryTheory.eqToHom (selectedObject_eq_pointed A y₀ hy₀ huniq
          (pointedSelectedObject A y₀ hy₀))).1 = f
    simp only [_root_.CategoryTheory.eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pointedDelooping_inv_hom_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pointedDelooping_inv_hom_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pointedDelooping_inv_hom_id ``Submission.DifferentialGeometry.Topology.VanKampen.pointedDelooping_inv_hom_id

theorem pointedDelooping_hom_inv_id {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (y₀ : Y) (hy₀ : y₀ ∈ A) (huniq : ∀ y ∈ A, y = y₀) :
    pointedDeloopingFunctor A y₀ hy₀ huniq ⋙ pointedDeloopingInverse A y₀ hy₀ =
      𝟭 (FundamentalGroupoidOn Y A) := by
  apply Functor.hext
  · intro z
    exact (selectedObject_eq_pointed A y₀ hy₀ huniq z).symm
  · intro x y f
    have hx := selectedObject_eq_pointed A y₀ hy₀ huniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ huniq y
    subst x
    subst y
    apply heq_of_eq
    apply Subtype.ext
    simp [pointedDeloopingFunctor, pointedDeloopingInverse]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.pointedDelooping_hom_inv_id then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.pointedDelooping_hom_inv_id"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.pointedDelooping_hom_inv_id ``Submission.DifferentialGeometry.Topology.VanKampen.pointedDelooping_hom_inv_id

theorem fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (f : C(Y, Z)) (hf : _root_.Set.MapsTo f A B)
    (hBuniq : ∀ z ∈ B, z = f y₀) :
    fundamentalGroupoidMapOn f hf ⋙
        pointedDeloopingFunctor B (f y₀) (hf hy₀) hBuniq =
      pointedDeloopingFunctor A y₀ hy₀ hAuniq ⋙
        (FundamentalGroup.map f y₀).toFunctor := by
  apply Functor.hext
  · intro z
    exact Subsingleton.elim _ _
  · intro x y g
    have hx := selectedObject_eq_pointed A y₀ hy₀ hAuniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ hAuniq y
    subst x
    subst y
    let pA := pointedSelectedObject A y₀ hy₀
    let pB := pointedSelectedObject B (f y₀) (hf hy₀)
    let J := fundamentalGroupoidMapOn f hf
    let iA := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A})
    let iB := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Z | z.as ∈ B})
    have q : J.obj pA = pB :=
      selectedObject_eq_pointed B (f y₀) (hf hy₀) hBuniq _
    have r : pA = pA := selectedObject_eq_pointed A y₀ hy₀ hAuniq pA
    have hBconj :
        (_root_.CategoryTheory.eqToHom q.symm ≫ J.map g ≫ _root_.CategoryTheory.eqToHom q) ≍ J.map g :=
      (_root_.CategoryTheory.conj_eqToHom_iff_heq' _ _ q.symm q).1 rfl
    have hBunder :
        iB.map (_root_.CategoryTheory.eqToHom q.symm ≫ J.map g ≫ _root_.CategoryTheory.eqToHom q) ≍ iB.map (J.map g) :=
      Functor.map_heq iB q.symm q.symm hBconj
    have hAconj :
        (_root_.CategoryTheory.eqToHom r.symm ≫ g ≫ _root_.CategoryTheory.eqToHom r) ≍ g :=
      (_root_.CategoryTheory.conj_eqToHom_iff_heq' _ _ r.symm r).1 rfl
    have hAunder :
        iA.map (_root_.CategoryTheory.eqToHom r.symm ≫ g ≫ _root_.CategoryTheory.eqToHom r) ≍ iA.map g :=
      Functor.map_heq iA r.symm r.symm hAconj
    have hAmap := Functor.map_heq (FundamentalGroupoid.map f)
      (congrArg iA.obj r.symm) (congrArg iA.obj r.symm) hAunder
    exact hBunder.trans hAmap.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor

theorem fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (z₀ : Z) (hz₀ : z₀ ∈ B)
    (hBuniq : ∀ z ∈ B, z = z₀) (f : C(Y, Z)) (hf : _root_.Set.MapsTo f A B)
    (hbase : f y₀ = z₀) :
    fundamentalGroupoidMapOn f hf ⋙ pointedDeloopingFunctor B z₀ hz₀ hBuniq =
      pointedDeloopingFunctor A y₀ hy₀ hAuniq ⋙
        (FundamentalGroup.mapOfEq f hbase).toFunctor := by
  apply Functor.hext
  · intro z
    exact Subsingleton.elim _ _
  · intro x y g
    have hx := selectedObject_eq_pointed A y₀ hy₀ hAuniq x
    have hy := selectedObject_eq_pointed A y₀ hy₀ hAuniq y
    subst x
    subst y
    let pA := pointedSelectedObject A y₀ hy₀
    let pB := pointedSelectedObject B z₀ hz₀
    let J := fundamentalGroupoidMapOn f hf
    let iA := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Y | z.as ∈ A})
    let iB := CategoryTheory.Subgroupoid.hom
      (CategoryTheory.Subgroupoid.full {z : FundamentalGroupoid Z | z.as ∈ B})
    have q : J.obj pA = pB := selectedObject_eq_pointed B z₀ hz₀ hBuniq _
    have r : pA = pA := selectedObject_eq_pointed A y₀ hy₀ hAuniq pA
    have hBconj : (_root_.CategoryTheory.eqToHom q.symm ≫ J.map g ≫ _root_.CategoryTheory.eqToHom q) ≍ J.map g :=
      (_root_.CategoryTheory.conj_eqToHom_iff_heq' _ _ q.symm q).1 rfl
    have hBunder :
        iB.map (_root_.CategoryTheory.eqToHom q.symm ≫ J.map g ≫ _root_.CategoryTheory.eqToHom q) ≍ iB.map (J.map g) :=
      Functor.map_heq iB q.symm q.symm hBconj
    have hAconj : (_root_.CategoryTheory.eqToHom r.symm ≫ g ≫ _root_.CategoryTheory.eqToHom r) ≍ g :=
      (_root_.CategoryTheory.conj_eqToHom_iff_heq' _ _ r.symm r).1 rfl
    have hAunder : iA.map (_root_.CategoryTheory.eqToHom r.symm ≫ g ≫ _root_.CategoryTheory.eqToHom r) ≍ iA.map g :=
      Functor.map_heq iA r.symm r.symm hAconj
    have hAmap := Functor.map_heq (FundamentalGroupoid.map f)
      (congrArg iA.obj r.symm) (congrArg iA.obj r.symm) hAunder
    have hcast (p : FundamentalGroup Y y₀) :
        FundamentalGroup.mapOfEq f hbase p ≍ FundamentalGroup.map f y₀ p := by
      rw [FundamentalGroup.mapOfEq_apply]
      exact Path.Homotopic.Quotient.cast_heq hbase.symm hbase.symm
    exact hBunder.trans
      ((hcast ((pointedDeloopingFunctor A y₀ hy₀ hAuniq).map g)).trans hAmap).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq

theorem fundamentalGroup_to_pointedDeloopingInverse_comp
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (f : C(Y, Z)) (hf : _root_.Set.MapsTo f A B)
    (hBuniq : ∀ z ∈ B, z = f y₀) :
    (FundamentalGroup.map f y₀).toFunctor ⋙
        pointedDeloopingInverse B (f y₀) (hf hy₀) =
      pointedDeloopingInverse A y₀ hy₀ ⋙ fundamentalGroupoidMapOn f hf := by
  let DA := pointedDeloopingFunctor A y₀ hy₀ hAuniq
  let DB := pointedDeloopingFunctor B (f y₀) (hf hy₀) hBuniq
  let EA := pointedDeloopingInverse A y₀ hy₀
  let EB := pointedDeloopingInverse B (f y₀) (hf hy₀)
  let J := fundamentalGroupoidMapOn f hf
  let m := (FundamentalGroup.map f y₀).toFunctor
  change m ⋙ EB = EA ⋙ J
  calc
    m ⋙ EB = (𝟭 _) ⋙ m ⋙ EB := rfl
    _ = (EA ⋙ DA) ⋙ m ⋙ EB := by
      rw [pointedDelooping_inv_hom_id A y₀ hy₀ hAuniq]
    _ = EA ⋙ (DA ⋙ m) ⋙ EB := rfl
    _ = EA ⋙ (J ⋙ DB) ⋙ EB := by
      rw [fundamentalGroupoidMapOn_comp_pointedDeloopingFunctor
        A B y₀ hy₀ hAuniq f hf hBuniq]
    _ = EA ⋙ J ⋙ (DB ⋙ EB) := rfl
    _ = EA ⋙ J ⋙ 𝟭 _ := by
      rw [pointedDelooping_hom_inv_id B (f y₀) (hf hy₀) hBuniq]
    _ = EA ⋙ J := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_to_pointedDeloopingInverse_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroup_to_pointedDeloopingInverse_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_to_pointedDeloopingInverse_comp ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroup_to_pointedDeloopingInverse_comp

theorem fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : Set Y) (B : Set Z) (y₀ : Y) (hy₀ : y₀ ∈ A)
    (hAuniq : ∀ y ∈ A, y = y₀) (z₀ : Z) (hz₀ : z₀ ∈ B)
    (hBuniq : ∀ z ∈ B, z = z₀) (f : C(Y, Z)) (hf : _root_.Set.MapsTo f A B)
    (hbase : f y₀ = z₀) :
    (FundamentalGroup.mapOfEq f hbase).toFunctor ⋙
        pointedDeloopingInverse B z₀ hz₀ =
      pointedDeloopingInverse A y₀ hy₀ ⋙ fundamentalGroupoidMapOn f hf := by
  let DA := pointedDeloopingFunctor A y₀ hy₀ hAuniq
  let DB := pointedDeloopingFunctor B z₀ hz₀ hBuniq
  let EA := pointedDeloopingInverse A y₀ hy₀
  let EB := pointedDeloopingInverse B z₀ hz₀
  let J := fundamentalGroupoidMapOn f hf
  let m := (FundamentalGroup.mapOfEq f hbase).toFunctor
  change m ⋙ EB = EA ⋙ J
  calc
    m ⋙ EB = (𝟭 _) ⋙ m ⋙ EB := rfl
    _ = (EA ⋙ DA) ⋙ m ⋙ EB := by
      rw [pointedDelooping_inv_hom_id A y₀ hy₀ hAuniq]
    _ = EA ⋙ (DA ⋙ m) ⋙ EB := rfl
    _ = EA ⋙ (J ⋙ DB) ⋙ EB := by
      rw [fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
        A B y₀ hy₀ hAuniq z₀ hz₀ hBuniq f hf hbase]
    _ = EA ⋙ J ⋙ (DB ⋙ EB) := rfl
    _ = EA ⋙ J ⋙ 𝟭 _ := by
      rw [pointedDelooping_hom_inv_id B z₀ hz₀ hBuniq]
    _ = EA ⋙ J := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp

abbrev overlapBasepoint {X : Type u} (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) : ↑(U ∩ V) :=
  ⟨x₀, hx₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.overlapBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.overlapBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.overlapBasepoint ``Submission.DifferentialGeometry.Topology.VanKampen.overlapBasepoint

abbrev leftBasepoint {X : Type u} (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) : U := ⟨x₀, hx₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.leftBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.leftBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.leftBasepoint ``Submission.DifferentialGeometry.Topology.VanKampen.leftBasepoint

abbrev rightBasepoint {X : Type u} (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) : V := ⟨x₀, hx₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.rightBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.rightBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.rightBasepoint ``Submission.DifferentialGeometry.Topology.VanKampen.rightBasepoint

theorem interToLeft_overlapBasepoint {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    (interToLeft U V) (overlapBasepoint U V x₀ hx₀) = leftBasepoint U x₀ hx₀.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint ``Submission.DifferentialGeometry.Topology.VanKampen.interToLeft_overlapBasepoint

theorem interToRight_overlapBasepoint {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    (interToRight U V) (overlapBasepoint U V x₀ hx₀) = rightBasepoint V x₀ hx₀.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.interToRight_overlapBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.interToRight_overlapBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.interToRight_overlapBasepoint ``Submission.DifferentialGeometry.Topology.VanKampen.interToRight_overlapBasepoint

theorem leftBasepoint_toAmbient {X : Type u} [TopologicalSpace X]
    (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    (subsetToAmbient U) (leftBasepoint U x₀ hx₀) = x₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.leftBasepoint_toAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.leftBasepoint_toAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.leftBasepoint_toAmbient ``Submission.DifferentialGeometry.Topology.VanKampen.leftBasepoint_toAmbient

theorem rightBasepoint_toAmbient {X : Type u} [TopologicalSpace X]
    (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    (subsetToAmbient V) (rightBasepoint V x₀ hx₀) = x₀ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.rightBasepoint_toAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.rightBasepoint_toAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.rightBasepoint_toAmbient ``Submission.DifferentialGeometry.Topology.VanKampen.rightBasepoint_toAmbient

theorem fundamentalGroup_mapOfEq_heq_map
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y₀ : Y) (z₀ : Z) (hbase : f y₀ = z₀)
    (p : FundamentalGroup Y y₀) :
    FundamentalGroup.mapOfEq f hbase p ≍ FundamentalGroup.map f y₀ p := by
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_heq hbase.symm hbase.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map

noncomputable def fundamentalGroupInterToLeft {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (interToLeft U V)
    (interToLeft_overlapBasepoint U V x₀ hx₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToLeft ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToLeft

noncomputable def fundamentalGroupInterToRight {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    GrpCat.of (FundamentalGroup (↑(U ∩ V)) (overlapBasepoint U V x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (interToRight U V)
    (interToRight_overlapBasepoint U V x₀ hx₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToRight ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupInterToRight

noncomputable def fundamentalGroupLeftToAmbient {X : Type u} [TopologicalSpace X]
    (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    GrpCat.of (FundamentalGroup U (leftBasepoint U x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (subsetToAmbient U)
    (leftBasepoint_toAmbient U x₀ hx₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient

noncomputable def fundamentalGroupRightToAmbient {X : Type u} [TopologicalSpace X]
    (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    GrpCat.of (FundamentalGroup V (rightBasepoint V x₀ hx₀)) ⟶
      GrpCat.of (FundamentalGroup X x₀) :=
  GrpCat.ofHom (FundamentalGroup.mapOfEq (subsetToAmbient V)
    (rightBasepoint_toAmbient V x₀ hx₀))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient

theorem fundamentalGroup_coverSquare_commutes {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    fundamentalGroupInterToLeft U V x₀ hx₀ ≫
        fundamentalGroupLeftToAmbient U x₀ hx₀.1 =
      fundamentalGroupInterToRight U V x₀ hx₀ ≫
        fundamentalGroupRightToAmbient V x₀ hx₀.2 := by
  apply GrpCat.ext
  intro p
  let hLU := interToLeft_overlapBasepoint U V x₀ hx₀
  let hRV := interToRight_overlapBasepoint U V x₀ hx₀
  let hUX := leftBasepoint_toAmbient U x₀ hx₀.1
  let hVX := rightBasepoint_toAmbient V x₀ hx₀.2
  have hInterL := fundamentalGroup_mapOfEq_heq_map
    (interToLeft U V) (overlapBasepoint U V x₀ hx₀)
      (leftBasepoint U x₀ hx₀.1) hLU p
  have hLeft := fundamentalGroup_mapOfEq_heq_map
    (subsetToAmbient U) (leftBasepoint U x₀ hx₀.1) x₀ hUX
      (FundamentalGroup.mapOfEq (interToLeft U V) hLU p)
  have hLeftMap := Functor.map_heq (FundamentalGroupoid.map (subsetToAmbient U))
    (congrArg FundamentalGroupoid.mk hLU.symm)
    (congrArg FundamentalGroupoid.mk hLU.symm) hInterL
  have hInterR := fundamentalGroup_mapOfEq_heq_map
    (interToRight U V) (overlapBasepoint U V x₀ hx₀)
      (rightBasepoint V x₀ hx₀.2) hRV p
  have hRight := fundamentalGroup_mapOfEq_heq_map
    (subsetToAmbient V) (rightBasepoint V x₀ hx₀.2) x₀ hVX
      (FundamentalGroup.mapOfEq (interToRight U V) hRV p)
  have hRightMap := Functor.map_heq (FundamentalGroupoid.map (subsetToAmbient V))
    (congrArg FundamentalGroupoid.mk hRV.symm)
    (congrArg FundamentalGroupoid.mk hRV.symm) hInterR
  have hSquare := Functor.hcongr_hom (fundamentalGroupoid_coverSquare_commutes U V) p
  exact eq_of_heq ((hLeft.trans hLeftMap).trans (hSquare.trans (hRight.trans hRightMap).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_coverSquare_commutes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroup_coverSquare_commutes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_coverSquare_commutes ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroup_coverSquare_commutes

def basedGroupSquareIsPushoutStatement {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) : Prop :=
  _root_.CategoryTheory.IsPushout
    (fundamentalGroupInterToLeft U V x₀ hx₀)
    (fundamentalGroupInterToRight U V x₀ hx₀)
    (fundamentalGroupLeftToAmbient U x₀ hx₀.1)
    (fundamentalGroupRightToAmbient V x₀ hx₀.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.basedGroupSquareIsPushoutStatement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.basedGroupSquareIsPushoutStatement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.basedGroupSquareIsPushoutStatement ``Submission.DifferentialGeometry.Topology.VanKampen.basedGroupSquareIsPushoutStatement

theorem selectedIn_singleton_mem {X : Type u} (B : Set X) (x₀ : X) (hx₀ : x₀ ∈ B) :
    leftBasepoint B x₀ hx₀ ∈ selectedIn ({x₀} : Set X) B := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_mem ``Submission.DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_mem

theorem eq_basepoint_of_mem_selectedIn_singleton {X : Type u}
    (B : Set X) (x₀ : X) (hx₀ : x₀ ∈ B) (y : B)
    (hy : y ∈ selectedIn ({x₀} : Set X) B) : y = leftBasepoint B x₀ hx₀ := by
  apply Subtype.ext
  exact hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.eq_basepoint_of_mem_selectedIn_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.eq_basepoint_of_mem_selectedIn_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.eq_basepoint_of_mem_selectedIn_singleton ``Submission.DifferentialGeometry.Topology.VanKampen.eq_basepoint_of_mem_selectedIn_singleton

theorem selectedIn_singleton_isRepresentative {X : Type u} [TopologicalSpace X]
    (B : Set X) [PathConnectedSpace B] (x₀ : X) (hx₀ : x₀ ∈ B) :
    IsRepresentative (selectedIn ({x₀} : Set X) B) := by
  intro y
  exact ⟨leftBasepoint B x₀ hx₀, selectedIn_singleton_mem B x₀ hx₀,
    PathConnectedSpace.joined _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_isRepresentative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_isRepresentative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_isRepresentative ``Submission.DifferentialGeometry.Topology.VanKampen.selectedIn_singleton_isRepresentative

theorem selectedInterToLeft_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    selectedInterToLeft ({x₀} : Set X) U V ⋙
        pointedDeloopingFunctor (selectedIn ({x₀} : Set X) U)
          (leftBasepoint U x₀ hx₀.1) (selectedIn_singleton_mem U x₀ hx₀.1)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀.1 y hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) (U ∩ V))
          (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton
            (U ∩ V) x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (interToLeft U V)
          (interToLeft_overlapBasepoint U V x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) (U ∩ V)) (selectedIn ({x₀} : Set X) U)
    (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton (U ∩ V) x₀ hx₀ y hy)
    (leftBasepoint U x₀ hx₀.1) (selectedIn_singleton_mem U x₀ hx₀.1)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀.1 y hy)
    (interToLeft U V) (fun _ h => h) (interToLeft_overlapBasepoint U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedInterToLeft_comp_pointedDelooping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedInterToLeft_comp_pointedDelooping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedInterToLeft_comp_pointedDelooping ``Submission.DifferentialGeometry.Topology.VanKampen.selectedInterToLeft_comp_pointedDelooping

theorem selectedInterToRight_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    selectedInterToRight ({x₀} : Set X) U V ⋙
        pointedDeloopingFunctor (selectedIn ({x₀} : Set X) V)
          (rightBasepoint V x₀ hx₀.2) (selectedIn_singleton_mem V x₀ hx₀.2)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀.2 y hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) (U ∩ V))
          (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton
            (U ∩ V) x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (interToRight U V)
          (interToRight_overlapBasepoint U V x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) (U ∩ V)) (selectedIn ({x₀} : Set X) V)
    (overlapBasepoint U V x₀ hx₀) (selectedIn_singleton_mem (U ∩ V) x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton (U ∩ V) x₀ hx₀ y hy)
    (rightBasepoint V x₀ hx₀.2) (selectedIn_singleton_mem V x₀ hx₀.2)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀.2 y hy)
    (interToRight U V) (fun _ h => h) (interToRight_overlapBasepoint U V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedInterToRight_comp_pointedDelooping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedInterToRight_comp_pointedDelooping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedInterToRight_comp_pointedDelooping ``Submission.DifferentialGeometry.Topology.VanKampen.selectedInterToRight_comp_pointedDelooping

theorem selectedLeftToAmbient_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    selectedLeftToAmbient ({x₀} : Set X) U ⋙
        pointedDeloopingFunctor ({x₀} : Set X) x₀ (Set.mem_singleton x₀)
          (fun _ hy => hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) U)
          (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (subsetToAmbient U)
          (leftBasepoint_toAmbient U x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) U) ({x₀} : Set X)
    (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient U) (fun _ h => h) (leftBasepoint_toAmbient U x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedLeftToAmbient_comp_pointedDelooping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedLeftToAmbient_comp_pointedDelooping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedLeftToAmbient_comp_pointedDelooping ``Submission.DifferentialGeometry.Topology.VanKampen.selectedLeftToAmbient_comp_pointedDelooping

theorem selectedRightToAmbient_comp_pointedDelooping {X : Type u} [TopologicalSpace X]
    (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    selectedRightToAmbient ({x₀} : Set X) V ⋙
        pointedDeloopingFunctor ({x₀} : Set X) x₀ (Set.mem_singleton x₀)
          (fun _ hy => hy) =
      pointedDeloopingFunctor (selectedIn ({x₀} : Set X) V)
          (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀)
          (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀ y hy) ⋙
        (FundamentalGroup.mapOfEq (subsetToAmbient V)
          (rightBasepoint_toAmbient V x₀ hx₀)).toFunctor := by
  exact fundamentalGroupoidMapOn_comp_pointedDeloopingFunctorOfEq
    (selectedIn ({x₀} : Set X) V) ({x₀} : Set X)
    (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient V) (fun _ h => h) (rightBasepoint_toAmbient V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.selectedRightToAmbient_comp_pointedDelooping then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.selectedRightToAmbient_comp_pointedDelooping"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.selectedRightToAmbient_comp_pointedDelooping ``Submission.DifferentialGeometry.Topology.VanKampen.selectedRightToAmbient_comp_pointedDelooping

theorem fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse
    {X : Type u} [TopologicalSpace X] (U : Set X) (x₀ : X) (hx₀ : x₀ ∈ U) :
    (FundamentalGroup.mapOfEq (subsetToAmbient U)
        (leftBasepoint_toAmbient U x₀ hx₀)).toFunctor ⋙
        pointedDeloopingInverse ({x₀} : Set X) x₀ (Set.mem_singleton x₀) =
      pointedDeloopingInverse (selectedIn ({x₀} : Set X) U)
          (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀) ⋙
        selectedLeftToAmbient ({x₀} : Set X) U := by
  exact fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp
    (selectedIn ({x₀} : Set X) U) ({x₀} : Set X)
    (leftBasepoint U x₀ hx₀) (selectedIn_singleton_mem U x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient U) (fun _ h => h) (leftBasepoint_toAmbient U x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse

theorem fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse
    {X : Type u} [TopologicalSpace X] (V : Set X) (x₀ : X) (hx₀ : x₀ ∈ V) :
    (FundamentalGroup.mapOfEq (subsetToAmbient V)
        (rightBasepoint_toAmbient V x₀ hx₀)).toFunctor ⋙
        pointedDeloopingInverse ({x₀} : Set X) x₀ (Set.mem_singleton x₀) =
      pointedDeloopingInverse (selectedIn ({x₀} : Set X) V)
          (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀) ⋙
        selectedRightToAmbient ({x₀} : Set X) V := by
  exact fundamentalGroupMapOfEq_to_pointedDeloopingInverse_comp
    (selectedIn ({x₀} : Set X) V) ({x₀} : Set X)
    (rightBasepoint V x₀ hx₀) (selectedIn_singleton_mem V x₀ hx₀)
    (fun y hy => eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀ y hy)
    x₀ (Set.mem_singleton x₀) (fun _ hy => hy)
    (subsetToAmbient V) (fun _ h => h) (rightBasepoint_toAmbient V x₀ hx₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse

theorem fundamentalGroup_isPushout {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ)
    (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))] :
    basedGroupSquareIsPushoutStatement U V x₀ hx₀ := by
  let AW := selectedIn ({x₀} : Set X) (U ∩ V)
  let AU := selectedIn ({x₀} : Set X) U
  let AV := selectedIn ({x₀} : Set X) V
  let AX : Set X := {x₀}
  let w₀ := overlapBasepoint U V x₀ hx₀
  let u₀ := leftBasepoint U x₀ hx₀.1
  let v₀ := rightBasepoint V x₀ hx₀.2
  have hw₀ : w₀ ∈ AW := selectedIn_singleton_mem (U ∩ V) x₀ hx₀
  have hu₀ : u₀ ∈ AU := selectedIn_singleton_mem U x₀ hx₀.1
  have hv₀ : v₀ ∈ AV := selectedIn_singleton_mem V x₀ hx₀.2
  have hx₀A : x₀ ∈ AX := Set.mem_singleton x₀
  have hWuniq : ∀ y ∈ AW, y = w₀ := fun y hy =>
    eq_basepoint_of_mem_selectedIn_singleton (U ∩ V) x₀ hx₀ y hy
  have hUuniq : ∀ y ∈ AU, y = u₀ := fun y hy =>
    eq_basepoint_of_mem_selectedIn_singleton U x₀ hx₀.1 y hy
  have hVuniq : ∀ y ∈ AV, y = v₀ := fun y hy =>
    eq_basepoint_of_mem_selectedIn_singleton V x₀ hx₀.2 y hy
  have hXuniq : ∀ y ∈ AX, y = x₀ := fun _ hy => hy
  let DW := pointedDeloopingFunctor AW w₀ hw₀ hWuniq
  let DU := pointedDeloopingFunctor AU u₀ hu₀ hUuniq
  let DV := pointedDeloopingFunctor AV v₀ hv₀ hVuniq
  let DX := pointedDeloopingFunctor AX x₀ hx₀A hXuniq
  let EU := pointedDeloopingInverse AU u₀ hu₀
  let EV := pointedDeloopingInverse AV v₀ hv₀
  let EX := pointedDeloopingInverse AX x₀ hx₀A
  let mWU := (FundamentalGroup.mapOfEq (interToLeft U V)
    (interToLeft_overlapBasepoint U V x₀ hx₀)).toFunctor
  let mWV := (FundamentalGroup.mapOfEq (interToRight U V)
    (interToRight_overlapBasepoint U V x₀ hx₀)).toFunctor
  let mUX := (FundamentalGroup.mapOfEq (subsetToAmbient U)
    (leftBasepoint_toAmbient U x₀ hx₀.1)).toFunctor
  let mVX := (FundamentalGroup.mapOfEq (subsetToAmbient V)
    (rightBasepoint_toAmbient V x₀ hx₀.2)).toFunctor
  have hselected := seifertVanKampenOn ({x₀} : Set X) U V hU hV hcover
    (selectedIn_singleton_isRepresentative U x₀ hx₀.1)
    (selectedIn_singleton_isRepresentative V x₀ hx₀.2)
    (selectedIn_singleton_isRepresentative (U ∩ V) x₀ hx₀)
  unfold basedGroupSquareIsPushoutStatement
  apply IsPushout.mk' (fundamentalGroup_coverSquare_commutes U V x₀ hx₀)
  · intro T φ φ' hφU hφV
    let _ : _root_.CategoryTheory.Groupoid (ULift.{u} (_root_.CategoryTheory.SingleObj T)) := uliftGroupoid (_root_.CategoryTheory.SingleObj T)
    let upT : _root_.CategoryTheory.SingleObj T ⥤ ULift.{u} (_root_.CategoryTheory.SingleObj T) := ULift.upFunctor
    let Pφ := DX ⋙ φ.hom.toFunctor ⋙ upT
    let Pφ' := DX ⋙ φ'.hom.toFunctor ⋙ upT
    have hUfun : mUX ⋙ φ.hom.toFunctor = mUX ⋙ φ'.hom.toFunctor := by
      simpa only [mUX, fundamentalGroupLeftToAmbient, GrpCat.hom_ofHom,
        GrpCat.hom_comp, MonoidHom.comp_toFunctor] using
        congrArg (fun k => k.hom.toFunctor) hφU
    have hVfun : mVX ⋙ φ.hom.toFunctor = mVX ⋙ φ'.hom.toFunctor := by
      simpa only [mVX, fundamentalGroupRightToAmbient, GrpCat.hom_ofHom,
        GrpCat.hom_comp, MonoidHom.comp_toFunctor] using
        congrArg (fun k => k.hom.toFunctor) hφV
    have hleft :
        selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ =
          selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ' := by
      calc
        selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ =
            (selectedLeftToAmbient ({x₀} : Set X) U ⋙ DX) ⋙
              φ.hom.toFunctor ⋙ upT := rfl
        _ = (DU ⋙ mUX) ⋙ φ.hom.toFunctor ⋙ upT := by
          rw [selectedLeftToAmbient_comp_pointedDelooping U x₀ hx₀.1]
        _ = DU ⋙ (mUX ⋙ φ.hom.toFunctor) ⋙ upT := rfl
        _ = DU ⋙ (mUX ⋙ φ'.hom.toFunctor) ⋙ upT := by rw [hUfun]
        _ = (DU ⋙ mUX) ⋙ φ'.hom.toFunctor ⋙ upT := rfl
        _ = (selectedLeftToAmbient ({x₀} : Set X) U ⋙ DX) ⋙
              φ'.hom.toFunctor ⋙ upT := by
          rw [selectedLeftToAmbient_comp_pointedDelooping U x₀ hx₀.1]
        _ = selectedLeftToAmbient ({x₀} : Set X) U ⋙ Pφ' := rfl
    have hright :
        selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ =
          selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ' := by
      calc
        selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ =
            (selectedRightToAmbient ({x₀} : Set X) V ⋙ DX) ⋙
              φ.hom.toFunctor ⋙ upT := rfl
        _ = (DV ⋙ mVX) ⋙ φ.hom.toFunctor ⋙ upT := by
          rw [selectedRightToAmbient_comp_pointedDelooping V x₀ hx₀.2]
        _ = DV ⋙ (mVX ⋙ φ.hom.toFunctor) ⋙ upT := rfl
        _ = DV ⋙ (mVX ⋙ φ'.hom.toFunctor) ⋙ upT := by rw [hVfun]
        _ = (DV ⋙ mVX) ⋙ φ'.hom.toFunctor ⋙ upT := rfl
        _ = (selectedRightToAmbient ({x₀} : Set X) V ⋙ DX) ⋙
              φ'.hom.toFunctor ⋙ upT := by
          rw [selectedRightToAmbient_comp_pointedDelooping V x₀ hx₀.2]
        _ = selectedRightToAmbient ({x₀} : Set X) V ⋙ Pφ' := rfl
    have hP : Pφ = Pφ' := hselected.hom_ext
      (W := Grpd.of (ULift.{u} (_root_.CategoryTheory.SingleObj T))) hleft hright
    have hup : φ.hom.toFunctor ⋙ upT = φ'.hom.toFunctor ⋙ upT := by
      calc
        φ.hom.toFunctor ⋙ upT = (𝟭 _) ⋙ φ.hom.toFunctor ⋙ upT := rfl
        _ = (EX ⋙ DX) ⋙ φ.hom.toFunctor ⋙ upT := by
          rw [pointedDelooping_inv_hom_id AX x₀ hx₀A hXuniq]
        _ = EX ⋙ Pφ := rfl
        _ = EX ⋙ Pφ' := by rw [hP]
        _ = (EX ⋙ DX) ⋙ φ'.hom.toFunctor ⋙ upT := rfl
        _ = (𝟭 _) ⋙ φ'.hom.toFunctor ⋙ upT := by
          rw [pointedDelooping_inv_hom_id AX x₀ hx₀A hXuniq]
        _ = φ'.hom.toFunctor ⋙ upT := rfl
    have hdown := congrArg (fun F => F ⋙ ULift.downFunctor) hup
    have hsingle : φ.hom.toFunctor = φ'.hom.toFunctor := by
      change φ.hom.toFunctor = φ'.hom.toFunctor at hdown
      exact hdown
    apply GrpCat.hom_ext
    exact (SingleObj.mapHom _ _).injective hsingle
  · intro T a b hab
    let _ : _root_.CategoryTheory.Groupoid (ULift.{u} (_root_.CategoryTheory.SingleObj T)) := uliftGroupoid (_root_.CategoryTheory.SingleObj T)
    let upT : _root_.CategoryTheory.SingleObj T ⥤ ULift.{u} (_root_.CategoryTheory.SingleObj T) := ULift.upFunctor
    let FU := DU ⋙ a.hom.toFunctor ⋙ upT
    let FV := DV ⋙ b.hom.toFunctor ⋙ upT
    have habfun : mWU ⋙ a.hom.toFunctor = mWV ⋙ b.hom.toFunctor := by
      simpa only [mWU, mWV, fundamentalGroupInterToLeft,
        fundamentalGroupInterToRight, GrpCat.hom_ofHom,
        GrpCat.hom_comp, MonoidHom.comp_toFunctor] using
        congrArg (fun k => k.hom.toFunctor) hab
    have hcompat :
        selectedInterToLeft ({x₀} : Set X) U V ⋙ FU =
          selectedInterToRight ({x₀} : Set X) U V ⋙ FV := by
      calc
        selectedInterToLeft ({x₀} : Set X) U V ⋙ FU =
            (selectedInterToLeft ({x₀} : Set X) U V ⋙ DU) ⋙
              a.hom.toFunctor ⋙ upT := rfl
        _ = (DW ⋙ mWU) ⋙ a.hom.toFunctor ⋙ upT := by
          rw [selectedInterToLeft_comp_pointedDelooping U V x₀ hx₀]
        _ = DW ⋙ (mWU ⋙ a.hom.toFunctor) ⋙ upT := rfl
        _ = DW ⋙ (mWV ⋙ b.hom.toFunctor) ⋙ upT := by rw [habfun]
        _ = (DW ⋙ mWV) ⋙ b.hom.toFunctor ⋙ upT := rfl
        _ = (selectedInterToRight ({x₀} : Set X) U V ⋙ DV) ⋙
              b.hom.toFunctor ⋙ upT := by
          rw [selectedInterToRight_comp_pointedDelooping U V x₀ hx₀]
        _ = selectedInterToRight ({x₀} : Set X) U V ⋙ FV := rfl
    obtain ⟨L, hUL, hVL⟩ := hselected.exists_desc
      (W := Grpd.of (ULift.{u} (_root_.CategoryTheory.SingleObj T))) FU FV hcompat
    change selectedLeftToAmbient ({x₀} : Set X) U ⋙ L = FU at hUL
    change selectedRightToAmbient ({x₀} : Set X) V ⋙ L = FV at hVL
    let L₀ := EX ⋙ L ⋙ ULift.downFunctor
    let lhom := (SingleObj.mapHom _ _).symm L₀
    let l : GrpCat.of (FundamentalGroup X x₀) ⟶ T := GrpCat.ofHom lhom
    have hupdown : upT ⋙ ULift.downFunctor = 𝟭 (_root_.CategoryTheory.SingleObj T) := rfl
    have hUfactorFun : mUX ⋙ L₀ = a.hom.toFunctor := by
      calc
        mUX ⋙ L₀ = (mUX ⋙ EX) ⋙ L ⋙ ULift.downFunctor := rfl
        _ = (EU ⋙ selectedLeftToAmbient ({x₀} : Set X) U) ⋙ L ⋙
              ULift.downFunctor := by
          rw [fundamentalGroupLeftToAmbient_comp_pointedDeloopingInverse U x₀ hx₀.1]
        _ = EU ⋙ (selectedLeftToAmbient ({x₀} : Set X) U ⋙ L) ⋙
              ULift.downFunctor := rfl
        _ = EU ⋙ FU ⋙ ULift.downFunctor :=
          congrArg (fun F => EU ⋙ F ⋙ ULift.downFunctor) hUL
        _ = (EU ⋙ DU) ⋙ a.hom.toFunctor ⋙ (upT ⋙ ULift.downFunctor) := rfl
        _ = (𝟭 _) ⋙ a.hom.toFunctor ⋙ 𝟭 _ := by
          rw [pointedDelooping_inv_hom_id AU u₀ hu₀ hUuniq, hupdown]
        _ = a.hom.toFunctor := rfl
    have hVfactorFun : mVX ⋙ L₀ = b.hom.toFunctor := by
      calc
        mVX ⋙ L₀ = (mVX ⋙ EX) ⋙ L ⋙ ULift.downFunctor := rfl
        _ = (EV ⋙ selectedRightToAmbient ({x₀} : Set X) V) ⋙ L ⋙
              ULift.downFunctor := by
          rw [fundamentalGroupRightToAmbient_comp_pointedDeloopingInverse V x₀ hx₀.2]
        _ = EV ⋙ (selectedRightToAmbient ({x₀} : Set X) V ⋙ L) ⋙
              ULift.downFunctor := rfl
        _ = EV ⋙ FV ⋙ ULift.downFunctor :=
          congrArg (fun F => EV ⋙ F ⋙ ULift.downFunctor) hVL
        _ = (EV ⋙ DV) ⋙ b.hom.toFunctor ⋙ (upT ⋙ ULift.downFunctor) := rfl
        _ = (𝟭 _) ⋙ b.hom.toFunctor ⋙ 𝟭 _ := by
          rw [pointedDelooping_inv_hom_id AV v₀ hv₀ hVuniq, hupdown]
        _ = b.hom.toFunctor := rfl
    refine ⟨l, ?_, ?_⟩
    · apply GrpCat.hom_ext
      apply (SingleObj.mapHom _ _).injective
      simpa only [mUX, fundamentalGroupLeftToAmbient, l, lhom,
        GrpCat.hom_comp, GrpCat.hom_ofHom,
        MonoidHom.comp_toFunctor, Equiv.apply_symm_apply] using hUfactorFun
    · apply GrpCat.hom_ext
      apply (SingleObj.mapHom _ _).injective
      simpa only [mVX, fundamentalGroupRightToAmbient, l, lhom,
        GrpCat.hom_comp, GrpCat.hom_ofHom,
        MonoidHom.comp_toFunctor, Equiv.apply_symm_apply] using hVfactorFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_isPushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.fundamentalGroup_isPushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.fundamentalGroup_isPushout ``Submission.DifferentialGeometry.Topology.VanKampen.fundamentalGroup_isPushout

end DifferentialGeometry.Topology.VanKampen
