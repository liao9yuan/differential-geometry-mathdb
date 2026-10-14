/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

/- Adapted from Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e
for DifferentialGeometry v0.1.3 / Mathlib v4.33.1. -/

public import Mathlib.Algebra.Homology.HomologicalComplexLimits

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Kernels and cokernels in categories of homological complexes

-/

public section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace HomologicalComplex
open _root_.HomologicalComplex

variable {ι C : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  {K L : HomologicalComplex C c} (f : K ⟶ L)

open _root_.HomologicalComplex in
lemma hasKernel_of_hasKernel_f [∀ i, _root_.CategoryTheory.Limits.HasKernel (f.f i)] : _root_.CategoryTheory.Limits.HasKernel f :=
  have (i : ι) : _root_.CategoryTheory.Limits.HasLimit (_root_.CategoryTheory.Limits.parallelPair f 0 ⋙ _root_.HomologicalComplex.eval C c i) :=
    hasLimit_of_iso (F := (_root_.CategoryTheory.Limits.parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  ⟨_, _root_.HomologicalComplex.isLimitConeOfHasLimitEval _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `HomologicalComplex.hasKernel_of_hasKernel_f then
    throwError "Refusing to shadow existing declaration HomologicalComplex.hasKernel_of_hasKernel_f"
  Lean.modifyEnv fun env => Lean.addAlias env `HomologicalComplex.hasKernel_of_hasKernel_f ``Submission.HomologicalComplex.hasKernel_of_hasKernel_f

open _root_.HomologicalComplex in
lemma hasCokernel_of_hasCokernel_f [∀ i, _root_.CategoryTheory.Limits.HasCokernel (f.f i)] : _root_.CategoryTheory.Limits.HasCokernel f :=
  have (i : ι) : _root_.CategoryTheory.Limits.HasColimit (_root_.CategoryTheory.Limits.parallelPair f 0 ⋙ _root_.HomologicalComplex.eval C c i) :=
    hasColimit_of_iso (F := (_root_.CategoryTheory.Limits.parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  ⟨_, _root_.HomologicalComplex.isColimitCoconeOfHasColimitEval _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `HomologicalComplex.hasCokernel_of_hasCokernel_f then
    throwError "Refusing to shadow existing declaration HomologicalComplex.hasCokernel_of_hasCokernel_f"
  Lean.modifyEnv fun env => Lean.addAlias env `HomologicalComplex.hasCokernel_of_hasCokernel_f ``Submission.HomologicalComplex.hasCokernel_of_hasCokernel_f

open _root_.HomologicalComplex in
lemma eval_preservesLimit_of_hasKernel_f [∀ i, _root_.CategoryTheory.Limits.HasKernel (f.f i)] (i : ι) :
    PreservesLimit (_root_.CategoryTheory.Limits.parallelPair f 0) (_root_.HomologicalComplex.eval C c i) :=
  have (i : ι) : _root_.CategoryTheory.Limits.HasLimit (_root_.CategoryTheory.Limits.parallelPair f 0 ⋙ _root_.HomologicalComplex.eval C c i) :=
    hasLimit_of_iso (F := (_root_.CategoryTheory.Limits.parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  _root_.CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
    (_root_.HomologicalComplex.isLimitConeOfHasLimitEval _) (limit.isLimit _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `HomologicalComplex.eval_preservesLimit_of_hasKernel_f then
    throwError "Refusing to shadow existing declaration HomologicalComplex.eval_preservesLimit_of_hasKernel_f"
  Lean.modifyEnv fun env => Lean.addAlias env `HomologicalComplex.eval_preservesLimit_of_hasKernel_f ``Submission.HomologicalComplex.eval_preservesLimit_of_hasKernel_f

open _root_.HomologicalComplex in
lemma eval_preservesColimit_of_hasCokernel_f [∀ i, _root_.CategoryTheory.Limits.HasCokernel (f.f i)] (i : ι) :
    PreservesColimit (_root_.CategoryTheory.Limits.parallelPair f 0) (_root_.HomologicalComplex.eval C c i) :=
  have (i : ι) : _root_.CategoryTheory.Limits.HasColimit (_root_.CategoryTheory.Limits.parallelPair f 0 ⋙ _root_.HomologicalComplex.eval C c i) :=
    hasColimit_of_iso (F := (_root_.CategoryTheory.Limits.parallelPair (f.f i) 0))
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm) (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))
  _root_.CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
    (_root_.HomologicalComplex.isColimitCoconeOfHasColimitEval _) (colimit.isColimit _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `HomologicalComplex.eval_preservesColimit_of_hasCokernel_f then
    throwError "Refusing to shadow existing declaration HomologicalComplex.eval_preservesColimit_of_hasCokernel_f"
  Lean.modifyEnv fun env => Lean.addAlias env `HomologicalComplex.eval_preservesColimit_of_hasCokernel_f ``Submission.HomologicalComplex.eval_preservesColimit_of_hasCokernel_f

end HomologicalComplex
