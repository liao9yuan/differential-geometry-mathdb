/-
Copyright (c) 2025 Yaël Dillies, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Joël Riou
-/
module

/- Adapted from Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e
for DifferentialGeometry v0.1.3 / Mathlib v4.33.1. -/

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

@[expose] public section

namespace CategoryTheory.Limits
open _root_.CategoryTheory _root_.CategoryTheory.Limits
variable {J C : Type*} [Category* J] [Category* C] [HasZeroMorphisms C]
  {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)

open _root_.CategoryTheory _root_.CategoryTheory.Limits in
lemma hasKernel_of_hasKernel_app [∀ j, _root_.CategoryTheory.Limits.HasKernel (f.app j)] : _root_.CategoryTheory.Limits.HasKernel f :=
  have (j : J) : _root_.CategoryTheory.Limits.HasLimit ((_root_.CategoryTheory.Limits.parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := _root_.CategoryTheory.Limits.parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  _root_.CategoryTheory.Limits.functorCategoryHasLimit _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CategoryTheory.Limits.hasKernel_of_hasKernel_app then
    throwError "Refusing to shadow existing declaration CategoryTheory.Limits.hasKernel_of_hasKernel_app"
  Lean.modifyEnv fun env => Lean.addAlias env `CategoryTheory.Limits.hasKernel_of_hasKernel_app ``Submission.CategoryTheory.Limits.hasKernel_of_hasKernel_app

open _root_.CategoryTheory _root_.CategoryTheory.Limits in
lemma hasCokernel_of_hasCokernel_app [∀ j, _root_.CategoryTheory.Limits.HasCokernel (f.app j)] : _root_.CategoryTheory.Limits.HasCokernel f :=
  have (j : J) : _root_.CategoryTheory.Limits.HasColimit ((_root_.CategoryTheory.Limits.parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := _root_.CategoryTheory.Limits.parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  _root_.CategoryTheory.Limits.functorCategoryHasColimit _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CategoryTheory.Limits.hasCokernel_of_hasCokernel_app then
    throwError "Refusing to shadow existing declaration CategoryTheory.Limits.hasCokernel_of_hasCokernel_app"
  Lean.modifyEnv fun env => Lean.addAlias env `CategoryTheory.Limits.hasCokernel_of_hasCokernel_app ``Submission.CategoryTheory.Limits.hasCokernel_of_hasCokernel_app

open _root_.CategoryTheory _root_.CategoryTheory.Limits in
lemma evaluation_preservesLimit_of_hasKernel_app [∀ j, _root_.CategoryTheory.Limits.HasKernel (f.app j)] (j : J) :
    PreservesLimit (_root_.CategoryTheory.Limits.parallelPair f 0) ((_root_.CategoryTheory.evaluation _ _).obj j) :=
  have (j : J) : _root_.CategoryTheory.Limits.HasLimit ((_root_.CategoryTheory.Limits.parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := _root_.CategoryTheory.Limits.parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  _root_.CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
    (_root_.CategoryTheory.Limits.combinedIsLimit (F := _root_.CategoryTheory.Limits.parallelPair f 0)
      (fun j ↦ _root_.CategoryTheory.Limits.getLimitCone ((_root_.CategoryTheory.Limits.parallelPair f 0).flip.obj j)))
    (limit.isLimit _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CategoryTheory.Limits.evaluation_preservesLimit_of_hasKernel_app then
    throwError "Refusing to shadow existing declaration CategoryTheory.Limits.evaluation_preservesLimit_of_hasKernel_app"
  Lean.modifyEnv fun env => Lean.addAlias env `CategoryTheory.Limits.evaluation_preservesLimit_of_hasKernel_app ``Submission.CategoryTheory.Limits.evaluation_preservesLimit_of_hasKernel_app

open _root_.CategoryTheory _root_.CategoryTheory.Limits in
lemma evaluation_preservesColimit_of_hasCokernel_app [∀ j, _root_.CategoryTheory.Limits.HasCokernel (f.app j)] (j : J) :
    PreservesColimit (_root_.CategoryTheory.Limits.parallelPair f 0) ((_root_.CategoryTheory.evaluation _ _).obj j) :=
  have (j : J) : _root_.CategoryTheory.Limits.HasColimit ((_root_.CategoryTheory.Limits.parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := _root_.CategoryTheory.Limits.parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  _root_.CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
    (_root_.CategoryTheory.Limits.combinedIsColimit (F := _root_.CategoryTheory.Limits.parallelPair f 0)
      (fun j ↦ _root_.CategoryTheory.Limits.getColimitCocone ((_root_.CategoryTheory.Limits.parallelPair f 0).flip.obj j)))
    (colimit.isColimit _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CategoryTheory.Limits.evaluation_preservesColimit_of_hasCokernel_app then
    throwError "Refusing to shadow existing declaration CategoryTheory.Limits.evaluation_preservesColimit_of_hasCokernel_app"
  Lean.modifyEnv fun env => Lean.addAlias env `CategoryTheory.Limits.evaluation_preservesColimit_of_hasCokernel_app ``Submission.CategoryTheory.Limits.evaluation_preservesColimit_of_hasCokernel_app

end CategoryTheory.Limits
