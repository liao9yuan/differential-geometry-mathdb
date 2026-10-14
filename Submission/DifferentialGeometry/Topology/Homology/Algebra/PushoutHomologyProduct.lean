/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homology.Algebra.PushoutHomologyDifference

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace DifferentialGeometry.HomologicalComplex

variable {k : Type*} [Ring k] {ι : Type*} {c : ComplexShape ι}
  {W X Y Z : HomologicalComplex (ModuleCat k) c}
  {f : W ⟶ X} {g : W ⟶ Y} {r : X ⟶ Z} {s : Y ⟶ Z}

theorem bijective_homologyMap_pair_of_pushout (sq : _root_.CategoryTheory.IsPushout f g r s) [_root_.CategoryTheory.Mono f]
    (i j : ι) (hij : c.Rel i j) (hi : Subsingleton (Z.homology i))
    (hj : Subsingleton (Z.homology j)) :
    Function.Bijective (fun a : W.homology j =>
      (_root_.HomologicalComplex.homologyMap f j a,
        _root_.HomologicalComplex.homologyMap g j a)) := by
  let S := DifferentialGeometry.ShortComplex.pushoutShortComplex sq
  have hS := DifferentialGeometry.ShortComplex.pushoutShortExact sq
  have hδ : hS.δ i j hij = 0 := by
    let _ := hi
    exact (ModuleCat.isZero_of_subsingleton (Z.homology i)).eq_of_src _ _
  have hmono : _root_.CategoryTheory.Mono (_root_.HomologicalComplex.homologyMap S.f j) :=
    (hS.homology_exact₁ i j hij).mono_g hδ
  constructor
  · intro a b hab
    apply (ModuleCat.mono_iff_injective _).mp hmono
    have hfst := congrArg Prod.fst hab
    have hsnd := congrArg Prod.snd hab
    dsimp only at hfst hsnd
    change _root_.HomologicalComplex.homologyMap (biprod.lift f (-g)) j a =
      _root_.HomologicalComplex.homologyMap (biprod.lift f (-g)) j b
    simp only [biprod.lift_eq, _root_.HomologicalComplex.homologyMap_add,
      _root_.HomologicalComplex.homologyMap_comp,
      _root_.HomologicalComplex.homologyMap_neg]
    change _root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) j
        (_root_.HomologicalComplex.homologyMap f j a) +
      _root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) j
        (-(_root_.HomologicalComplex.homologyMap g j a)) =
      _root_.HomologicalComplex.homologyMap (biprod.inl : X ⟶ X ⊞ Y) j
        (_root_.HomologicalComplex.homologyMap f j b) +
      _root_.HomologicalComplex.homologyMap (biprod.inr : Y ⟶ X ⊞ Y) j
        (-(_root_.HomologicalComplex.homologyMap g j b))
    rw [hfst, hsnd]
  · rintro ⟨x, y⟩
    obtain ⟨a, ha, hb⟩ := exists_homology_preimage_of_pushout_eq sq j x y (hj.elim _ _)
    exact ⟨a, Prod.ext ha hb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.HomologicalComplex.bijective_homologyMap_pair_of_pushout then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.HomologicalComplex.bijective_homologyMap_pair_of_pushout"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.HomologicalComplex.bijective_homologyMap_pair_of_pushout ``Submission.DifferentialGeometry.HomologicalComplex.bijective_homologyMap_pair_of_pushout

end DifferentialGeometry.HomologicalComplex
