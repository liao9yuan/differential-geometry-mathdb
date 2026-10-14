/-
Copyright (c) 2025 Yaël Dillies, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Joël Riou
-/
module

/- Adapted from Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e
for DifferentialGeometry v0.1.3 / Mathlib v4.33.1. -/

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

@[expose] public section

namespace CategoryTheory.Limits
variable {J C : Type*} [Category* J] [Category* C] [HasZeroMorphisms C]
  {F₁ F₂ : J ⥤ C} (f : F₁ ⟶ F₂)

lemma hasKernel_of_hasKernel_app [∀ j, HasKernel (f.app j)] : HasKernel f :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  functorCategoryHasLimit _

lemma hasCokernel_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] : HasCokernel f :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  functorCategoryHasColimit _

lemma evaluation_preservesLimit_of_hasKernel_app [∀ j, HasKernel (f.app j)] (j : J) :
    PreservesLimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasLimit ((parallelPair f 0).flip.obj j) :=
    hasLimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  preservesLimit_of_preserves_limit_cone
    (combinedIsLimit (F := parallelPair f 0)
      (fun j ↦ getLimitCone ((parallelPair f 0).flip.obj j)))
    (limit.isLimit _)

lemma evaluation_preservesColimit_of_hasCokernel_app [∀ j, HasCokernel (f.app j)] (j : J) :
    PreservesColimit (parallelPair f 0) ((evaluation _ _).obj j) :=
  have (j : J) : HasColimit ((parallelPair f 0).flip.obj j) :=
    hasColimit_of_iso (F := parallelPair (f.app j) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  preservesColimit_of_preserves_colimit_cocone
    (combinedIsColimit (F := parallelPair f 0)
      (fun j ↦ getColimitCocone ((parallelPair f 0).flip.obj j)))
    (colimit.isColimit _)

end CategoryTheory.Limits
