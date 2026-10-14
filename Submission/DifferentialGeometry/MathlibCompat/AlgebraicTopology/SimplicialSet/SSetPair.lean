/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

/- Adapted from Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e
for DifferentialGeometry v0.1.3 / Mathlib v4.33.1. -/

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.MorphismProperty.Comma

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Pairs of simplicial sets

In this file, we define the category `SSetPair` of pairs of simplicial
sets, which consist of monomorphisms `i : X ⟶ Y` of simplicial sets.

-/

@[expose] public section

open _root_.Simplicial _root_.CategoryTheory

universe u

/-- The category `SSetPair` is the category of pairs of simplicial sets,
i.e. monomorphisms `i : X ⟶ Y`, see `SSetPair.of`. -/
abbrev SSetPair : Type (u + 1) := MorphismProperty.Arrow (.monomorphisms SSet.{u}) ⊤ ⊤

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair then
    throwError "Refusing to shadow existing declaration SSetPair"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair ``Submission.SSetPair

namespace SSetPair

instance _root_.Submission.SSetPair.instMonoSSetHom (P : SSetPair.{u}) : _root_.CategoryTheory.Mono P.hom := P.prop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoSSetHom then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoSSetHom"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoSSetHom ``Submission.SSetPair.instMonoSSetHom

/-- Constructor for `SSetPair`. -/
abbrev of {X Y : SSet.{u}} (i : X ⟶ Y) [_root_.CategoryTheory.Mono i] : SSetPair.{u} :=
  MorphismProperty.Arrow.mk i (by assumption)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.of then
    throwError "Refusing to shadow existing declaration SSetPair.of"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.of ``Submission.SSetPair.of

/-- The forget functor from `SSetPair` to the category `Arrow SSet`. -/
abbrev forget : SSetPair.{u} ⥤ _root_.CategoryTheory.Arrow SSet.{u} :=
  MorphismProperty.Arrow.forget _ _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.forget then
    throwError "Refusing to shadow existing declaration SSetPair.forget"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.forget ``Submission.SSetPair.forget

/-- Constructor for morphisms in `SSetPair`. -/
abbrev homMk {X Y : SSetPair.{u}} (left : X.left ⟶ Y.left) (right : X.right ⟶ Y.right)
    (w : left ≫ Y.hom = X.hom ≫ right := by cat_disch) : X ⟶ Y :=
  MorphismProperty.Arrow.Hom.mk (Arrow.homMk left right w) (by simp) (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homMk then
    throwError "Refusing to shadow existing declaration SSetPair.homMk"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homMk ``Submission.SSetPair.homMk

end SSetPair

open _root_.SSet _root_.SSet.Subcomplex in
/-- Given a subcomplex `A` of a simplical set `X`, this is the pair in `SSetPair`
corresponding to the inclusion `A.ι : (A : SSet) ⟶ X`. -/
abbrev SSet.Subcomplex.pair {X : SSet.{u}} (A : X.Subcomplex) : SSetPair.{u} := .of A.ι

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.SSet
  Lean.modifyEnv fun env => env.registerNamespace `Submission.SSet.Subcomplex
  let env ← Lean.getEnv
  if env.contains `SSet.Subcomplex.pair then
    throwError "Refusing to shadow existing declaration SSet.Subcomplex.pair"
  Lean.modifyEnv fun env => Lean.addAlias env `SSet.Subcomplex.pair ``Submission.SSet.Subcomplex.pair

open _root_.SSet _root_.SSet.Subcomplex in
/-- Given `X : SSet`, this is the functor `X.Subcomplex ⥤ SSetPair` which sends
`A : X.Subcomplex` to the pair corresponding to the inclusion `A.ι : (A : SSet) ⟶ X`. -/
@[implicit_reducible, simps]
def SSet.Subcomplex.toPairFunctor (X : SSet.{u}) : X.Subcomplex ⥤ SSetPair.{u} where
  obj := pair
  map f := SSetPair.homMk (SSet.Subcomplex.homOfLE f.le) (𝟙 _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSet.Subcomplex.toPairFunctor then
    throwError "Refusing to shadow existing declaration SSet.Subcomplex.toPairFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `SSet.Subcomplex.toPairFunctor ``Submission.SSet.Subcomplex.toPairFunctor

open _root_.SSet in
/-- If `X` is a simplicial set, this is the pair in `SSetPair` corresponding
to the inclusion of the empty subcomplex in `X`. -/
abbrev SSet.pair (X : SSet.{u}) : SSetPair.{u} := SSet.Subcomplex.pair (X := X) ⊥

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSet.pair then
    throwError "Refusing to shadow existing declaration SSet.pair"
  Lean.modifyEnv fun env => Lean.addAlias env `SSet.pair ``Submission.SSet.pair

open _root_.SSet in
/-- The functor `SSet ⥤ SSetPair` which sends `X : SSet` to the pair
corresponding to the inclusion of the empty subcomplex in `X`. -/
@[implicit_reducible, simps]
def SSet.toPairFunctor : SSet.{u} ⥤ SSetPair.{u} where
  obj := SSet.pair
  map f := SSetPair.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ f) (fun _ _ h ↦ by simp at h)) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSet.toPairFunctor then
    throwError "Refusing to shadow existing declaration SSet.toPairFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `SSet.toPairFunctor ``Submission.SSet.toPairFunctor
