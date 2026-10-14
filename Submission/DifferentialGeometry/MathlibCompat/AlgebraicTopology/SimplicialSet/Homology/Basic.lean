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

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

@[expose] public section

open _root_.Simplicial _root_.CategoryTheory _root_.CategoryTheory.Limits

universe w

namespace SSet
open _root_.SSet

variable {X : SSet.{w}} in
lemma Nonempty.mk {n : SimplexCategoryᵒᵖ} (x : X.obj n) : X.Nonempty :=
  ⟨X.map (SimplexCategory.const _ _ 0).op x⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.SSet.Nonempty
  let env ← Lean.getEnv
  if env.contains `SSet.Nonempty.mk then
    throwError "Refusing to shadow existing declaration SSet.Nonempty.mk"
  Lean.modifyEnv fun env => Lean.addAlias env `SSet.Nonempty.mk ``Submission.SSet.Nonempty.mk

variable {C : Type*} [Category* C] [HasCoproducts.{w} C] [Preadditive C]
  (X : SSet.{w}) (R : C)

open _root_.SSet in
lemma isZero_chainComplex [X.HasDimensionLT 0] :
    IsZero (X.chainComplex R) := by
  rw [IsZero.iff_id_eq_zero]
  ext n x
  exact ((X.notNonempty_iff_hasDimensionLT_zero.mpr inferInstance) (.mk x)).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSet.isZero_chainComplex then
    throwError "Refusing to shadow existing declaration SSet.isZero_chainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSet.isZero_chainComplex ``Submission.SSet.isZero_chainComplex

end SSet
