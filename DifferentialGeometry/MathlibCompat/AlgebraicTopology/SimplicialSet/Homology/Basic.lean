/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

Selected declarations adapted from Mathlib commit
c55e6e786f49471c72fbddbec5415808896aec1e for Mathlib v4.33.1.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty

@[expose] public section

open Simplicial CategoryTheory Limits

universe w

namespace SSet

variable {X : SSet.{w}} in
lemma Nonempty.mk {n : SimplexCategoryᵒᵖ} (x : X.obj n) : X.Nonempty :=
  ⟨X.map (SimplexCategory.const _ _ 0).op x⟩

variable {C : Type*} [Category* C] [HasCoproducts.{w} C] [Preadditive C]
  (X : SSet.{w}) (R : C)

lemma isZero_chainComplex [X.HasDimensionLT 0] :
    IsZero (X.chainComplex R) := by
  rw [IsZero.iff_id_eq_zero]
  ext n x
  exact ((X.notNonempty_iff_hasDimensionLT_zero.mpr inferInstance) (.mk x)).elim

end SSet
