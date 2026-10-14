/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

/- Adapted from Mathlib commit c55e6e786f49471c72fbddbec5415808896aec1e
for DifferentialGeometry v0.1.3 / Mathlib v4.33.1. -/

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Submission.DifferentialGeometry.MathlibCompat.Algebra.Homology.HomologicalComplexKernels
public import Mathlib.Algebra.Homology.HomologySequence
public import Submission.DifferentialGeometry.MathlibCompat.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Submission.DifferentialGeometry.MathlibCompat.AlgebraicTopology.SimplicialSet.SSetPair
public import Submission.DifferentialGeometry.MathlibCompat.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Relative simplicial homology

In this file, given a pair `P : SSetPair` of simplicial sets,
we define the chain complex `P.chainComplex R` of `P` with coefficients
in `R` (where `R` is an object in a preadditive category with
coproducts). The homology in degree `n` of this complex is denoted `P.homology R n`:
this is the relative homology of the pair, which is related to the homology
of simplicial sets `P.left` and `P.right` via a long homology sequence
(see the lemmas `SSetPair.homology_exact₁`, `SSetPair.homology_exact₂` and
`SSetPair.homology_exact₃`),

-/

@[expose] public section

open _root_.Simplicial _root_.CategoryTheory _root_.Submission.CategoryTheory _root_.CategoryTheory.Limits _root_.Submission.CategoryTheory.Limits _root_.Opposite

universe w

namespace SSetPair

section

variable (C : Type*) [Category* C] [HasCoproducts.{w} C] [Preadditive C]

/-- The bifunctor which sends `R : C` and a pair of simplicial sets `i : X ⟶ Y`
(with `i` a monomorphism) to `X.chainComplex R`, which is the
chain complex of `X` with coefficients in `R` (the usual one is for `C := Ab`
and `R := ℤ`.). -/
noncomputable abbrev chainComplexFunctorLeft :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft ..).obj
    (SSetPair.forget ⋙ Arrow.leftFunc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexFunctorLeft then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexFunctorLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexFunctorLeft ``Submission.SSetPair.chainComplexFunctorLeft

/-- The bifunctor which sends `R : C` and a pair of simplicial sets `i : X ⟶ Y`
(with `i` a monomorphism) to `Y.chainComplex R`, which is the
chain complex of `Y` with coefficients in `R` (the usual one is for `C := Ab`
and `R := ℤ`.). -/
noncomputable abbrev chainComplexFunctorRight :
    C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  SSet.chainComplexFunctor.{w} C ⋙ (Functor.whiskeringLeft ..).obj
    (SSetPair.forget ⋙ Arrow.rightFunc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexFunctorRight then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexFunctorRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexFunctorRight ``Submission.SSetPair.chainComplexFunctorRight

/-- The map `X.chainComplex R ⟶ Y.chainComplex R` for each pair of simplicial
sets `i : X ⟶ Y` (with `i` a monomorphism), and `R : C`, as a natural transformation of
bifunctors `C ⥤ SSetPair ⥤ ChainComplex C ℕ`. -/
noncomputable abbrev chainComplexFunctorLeftToRight :
    chainComplexFunctorLeft.{w} C ⟶ chainComplexFunctorRight.{w} C :=
  Functor.whiskerLeft _ ((Functor.whiskeringLeft ..).map
    (Functor.whiskerLeft _ Arrow.leftToRight))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexFunctorLeftToRight ``Submission.SSetPair.chainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instMonoFNatChainComplexMapHomSSet (R : C) (P : SSetPair.{w}) (n : ℕ) :
    Mono ((SSet.chainComplexMap P.hom R).f n) :=
  inferInstanceAs (_root_.CategoryTheory.Mono ((sigmaConst.obj R).map (P.hom.app (_root_.Opposite.op ⦋n⦌))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoFNatChainComplexMapHomSSet then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoFNatChainComplexMapHomSSet"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoFNatChainComplexMapHomSSet ``Submission.SSetPair.instMonoFNatChainComplexMapHomSSet

instance _root_.Submission.SSetPair.instMonoChainComplexNatChainComplexMapHomSSet (R : C) (P : SSetPair.{w}) :
    Mono (SSet.chainComplexMap P.hom R) :=
  HomologicalComplex.mono_of_mono_f _ inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoChainComplexNatChainComplexMapHomSSet then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoChainComplexNatChainComplexMapHomSSet"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoChainComplexNatChainComplexMapHomSSet ``Submission.SSetPair.instMonoChainComplexNatChainComplexMapHomSSet

instance _root_.Submission.SSetPair.instMonoFNatAppChainComplexFunctorChainComplexFunctorLeftToRight (R : C) (P : SSetPair.{w}) (n : ℕ) :
    Mono ((((chainComplexFunctorLeftToRight C).app R).app P).f n) :=
  inferInstanceAs (_root_.CategoryTheory.Mono ((SSet.chainComplexMap P.hom R).f n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoFNatAppChainComplexFunctorChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoFNatAppChainComplexFunctorChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoFNatAppChainComplexFunctorChainComplexFunctorLeftToRight ``Submission.SSetPair.instMonoFNatAppChainComplexFunctorChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instMonoChainComplexNatAppFunctorChainComplexFunctorLeftToRight (R : C) (P : SSetPair.{w}) :
    Mono (((chainComplexFunctorLeftToRight C).app R).app P) :=
  inferInstanceAs (_root_.CategoryTheory.Mono (SSet.chainComplexMap P.hom R))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoChainComplexNatAppFunctorChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoChainComplexNatAppFunctorChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoChainComplexNatAppFunctorChainComplexFunctorLeftToRight ``Submission.SSetPair.instMonoChainComplexNatAppFunctorChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instMonoFunctorChainComplexNatAppChainComplexFunctorLeftToRight (R : C) : _root_.CategoryTheory.Mono ((chainComplexFunctorLeftToRight C).app R) :=
  NatTrans.mono_of_mono_app _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoFunctorChainComplexNatAppChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoFunctorChainComplexNatAppChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoFunctorChainComplexNatAppChainComplexFunctorLeftToRight ``Submission.SSetPair.instMonoFunctorChainComplexNatAppChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instMonoFunctorChainComplexNatChainComplexFunctorLeftToRight : _root_.CategoryTheory.Mono (chainComplexFunctorLeftToRight C) :=
  NatTrans.mono_of_mono_app _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instMonoFunctorChainComplexNatChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instMonoFunctorChainComplexNatChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instMonoFunctorChainComplexNatChainComplexFunctorLeftToRight ``Submission.SSetPair.instMonoFunctorChainComplexNatChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instHasCokernelFNatAppChainComplexFunctorChainComplexFunctorLeftToRight (R : C) (P : SSetPair.{w}) (n : ℕ) :
    HasCokernel ((((chainComplexFunctorLeftToRight C).app R).app P).f n) := by
  change _root_.CategoryTheory.Limits.HasCokernel ((sigmaConst.obj R).map (P.hom.app (_root_.Opposite.op ⦋n⦌)))
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instHasCokernelFNatAppChainComplexFunctorChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instHasCokernelFNatAppChainComplexFunctorChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instHasCokernelFNatAppChainComplexFunctorChainComplexFunctorLeftToRight ``Submission.SSetPair.instHasCokernelFNatAppChainComplexFunctorChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instHasCokernelFNatChainComplexMapHomSSet (R : C) (P : SSetPair.{w}) (n : ℕ) :
    HasCokernel ((SSet.chainComplexMap P.hom R).f n) :=
  inferInstanceAs (_root_.CategoryTheory.Limits.HasCokernel ((((chainComplexFunctorLeftToRight C).app R).app P).f n))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instHasCokernelFNatChainComplexMapHomSSet then
    throwError "Refusing to shadow existing declaration SSetPair.instHasCokernelFNatChainComplexMapHomSSet"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instHasCokernelFNatChainComplexMapHomSSet ``Submission.SSetPair.instHasCokernelFNatChainComplexMapHomSSet

instance _root_.Submission.SSetPair.instHasCokernelChainComplexNatAppFunctorChainComplexFunctorLeftToRight (R : C) (P : SSetPair.{w}) :
    HasCokernel (((chainComplexFunctorLeftToRight C).app R).app P) :=
  HomologicalComplex.hasCokernel_of_hasCokernel_f _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instHasCokernelChainComplexNatAppFunctorChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instHasCokernelChainComplexNatAppFunctorChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instHasCokernelChainComplexNatAppFunctorChainComplexFunctorLeftToRight ``Submission.SSetPair.instHasCokernelChainComplexNatAppFunctorChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instHasCokernelFunctorChainComplexNatAppChainComplexFunctorLeftToRight (R : C) : _root_.CategoryTheory.Limits.HasCokernel ((chainComplexFunctorLeftToRight C).app R) :=
  hasCokernel_of_hasCokernel_app _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instHasCokernelFunctorChainComplexNatAppChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instHasCokernelFunctorChainComplexNatAppChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instHasCokernelFunctorChainComplexNatAppChainComplexFunctorLeftToRight ``Submission.SSetPair.instHasCokernelFunctorChainComplexNatAppChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instHasCokernelFunctorChainComplexNatChainComplexFunctorLeftToRight : _root_.CategoryTheory.Limits.HasCokernel (chainComplexFunctorLeftToRight.{w} C) :=
  hasCokernel_of_hasCokernel_app _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instHasCokernelFunctorChainComplexNatChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.instHasCokernelFunctorChainComplexNatChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instHasCokernelFunctorChainComplexNatChainComplexFunctorLeftToRight ``Submission.SSetPair.instHasCokernelFunctorChainComplexNatChainComplexFunctorLeftToRight

/--
The relative chain complex associated to a *pair* of simplicial sets, with
coefficients in `R : C`, as a bifunctor `C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ`.
It computes the simplicial homology of a pair of simplicial sets with coefficients
in `R`. One can recover the ordinary relative simplicial chain complex when `C := Ab`
and `R := ℤ`.
-/
@[no_expose]
noncomputable def chainComplexFunctor : C ⥤ SSetPair.{w} ⥤ ChainComplex C ℕ :=
  _root_.CategoryTheory.Limits.cokernel (chainComplexFunctorLeftToRight.{w} C)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexFunctor then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexFunctor ``Submission.SSetPair.chainComplexFunctor

/--
For any pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and any `R : C`, this is the map from the chain complex of `Y`
(with coefficients in `R`) to the chain complex of the pair,
as a natural transformation of bifunctors `C ⥤ SSetPair ⥤ ChainComplex C ℕ`.
-/
@[no_expose]
noncomputable def chainComplexFunctorπ :
    chainComplexFunctorRight.{w} C ⟶ chainComplexFunctor.{w} C :=
  cokernel.π _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexFunctorπ then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexFunctorπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexFunctorπ ``Submission.SSetPair.chainComplexFunctorπ

instance _root_.Submission.SSetPair.instEpiFunctorChainComplexNatChainComplexFunctorπ : _root_.CategoryTheory.Epi (chainComplexFunctorπ.{w} C) := coequalizer.π_epi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instEpiFunctorChainComplexNatChainComplexFunctorπ then
    throwError "Refusing to shadow existing declaration SSetPair.instEpiFunctorChainComplexNatChainComplexFunctorπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instEpiFunctorChainComplexNatChainComplexFunctorπ ``Submission.SSetPair.instEpiFunctorChainComplexNatChainComplexFunctorπ

@[reassoc (attr := simp)]
lemma chainComplexFunctor_condition :
    chainComplexFunctorLeftToRight C ≫ chainComplexFunctorπ.{w} C = 0 :=
  cokernel.condition _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexFunctor_condition then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexFunctor_condition"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexFunctor_condition ``Submission.SSetPair.chainComplexFunctor_condition

/-- The (colimit) cokernel cofork expressing the bifunctor
`SSetPair.chainComplexFunctor C : C ⥤ SSetPair ⥤ ChainComplex C ℕ`
as a cokernel of `chainComplexFunctorLeftToRight C`. -/
noncomputable abbrev cokernelCoforkChainComplexFunctorLeftToRight :
    CokernelCofork (chainComplexFunctorLeftToRight.{w} C) :=
  CokernelCofork.ofπ _ (chainComplexFunctor_condition _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.cokernelCoforkChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.cokernelCoforkChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.cokernelCoforkChainComplexFunctorLeftToRight ``Submission.SSetPair.cokernelCoforkChainComplexFunctorLeftToRight

/-- The bifunctor `SSetPair.chainComplexFunctor C : C ⥤ SSetPair ⥤ ChainComplex C ℕ`
is a cokernel of `chainComplexFunctorLeftToRight C`. -/
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplexFunctorLeftToRight :
    IsColimit (cokernelCoforkChainComplexFunctorLeftToRight.{w} C) :=
  _root_.CategoryTheory.Limits.cokernelIsCokernel _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.isColimitCokernelCoforkChainComplexFunctorLeftToRight then
    throwError "Refusing to shadow existing declaration SSetPair.isColimitCokernelCoforkChainComplexFunctorLeftToRight"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.isColimitCokernelCoforkChainComplexFunctorLeftToRight ``Submission.SSetPair.isColimitCokernelCoforkChainComplexFunctorLeftToRight

instance _root_.Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation (R : C) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      ((_root_.CategoryTheory.evaluation ..).obj R) :=
  evaluation_preservesColimit_of_hasCokernel_app ..

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation ``Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation

instance _root_.Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairAppChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvaluation (R : C) (P : SSetPair.{w}) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair ((chainComplexFunctorLeftToRight.{w} C).app R) 0)
      ((_root_.CategoryTheory.evaluation ..).obj P) :=
  evaluation_preservesColimit_of_hasCokernel_app ..

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairAppChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvaluation then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairAppChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairAppChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvaluation ``Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairAppChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvaluation

instance _root_.Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairCompParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation (R : C) (P : SSetPair.{w}) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair (chainComplexFunctorLeftToRight.{w} C) 0 ⋙
      (_root_.CategoryTheory.evaluation ..).obj R) ((_root_.CategoryTheory.evaluation ..).obj P) :=
  _root_.CategoryTheory.Limits.preservesColimit_of_iso_diagram
    (K₁ := _root_.CategoryTheory.Limits.parallelPair ((chainComplexFunctorLeftToRight.{w} C).app R) 0) _
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairCompParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairCompParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairCompParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation ``Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairCompParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluation

instance _root_.Submission.SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairAppFunctorChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvalDown (R : C) (P : SSetPair.{w}) (n : ℕ) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair (((chainComplexFunctorLeftToRight.{w} C).app R).app P) 0)
      (HomologicalComplex.eval _ _ n) :=
  HomologicalComplex.eval_preservesColimit_of_hasCokernel_f ..

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairAppFunctorChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvalDown then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairAppFunctorChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvalDown"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairAppFunctorChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvalDown ``Submission.SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairAppFunctorChainComplexFunctorLeftToRightOfNatHomObjChainComplexFunctorLeftChainComplexFunctorRightEvalDown

instance _root_.Submission.SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairCompFunctorParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluationEvalDown (R : C) (P : SSetPair.{w}) (n : ℕ) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair (chainComplexFunctorLeftToRight.{w} C) 0 ⋙
      ((_root_.CategoryTheory.evaluation ..).obj R ⋙ (_root_.CategoryTheory.evaluation ..).obj P))
      (HomologicalComplex.eval _ _ n) :=
  _root_.CategoryTheory.Limits.preservesColimit_of_iso_diagram
    (K₁ := _root_.CategoryTheory.Limits.parallelPair (((chainComplexFunctorLeftToRight.{w} C).app R).app P) 0) _
      (parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
        (by dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairCompFunctorParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluationEvalDown then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairCompFunctorParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluationEvalDown"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairCompFunctorParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluationEvalDown ``Submission.SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairCompFunctorParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightObjEvaluationEvalDown

instance _root_.Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightCompObjEvaluationEvalDown (R : C) (P : SSetPair.{w}) (n : ℕ) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair (chainComplexFunctorLeftToRight.{w} C) 0)
      ((_root_.CategoryTheory.evaluation ..).obj R ⋙ (_root_.CategoryTheory.evaluation ..).obj P ⋙ HomologicalComplex.eval _ _ n) :=
  _root_.CategoryTheory.Limits.preservesColimit_of_natIso _ (Functor.associator ..)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightCompObjEvaluationEvalDown then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightCompObjEvaluationEvalDown"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightCompObjEvaluationEvalDown ``Submission.SSetPair.instPreservesColimitFunctorChainComplexNatWalkingParallelPairParallelPairChainComplexFunctorLeftToRightOfNatHomChainComplexFunctorLeftChainComplexFunctorRightCompObjEvaluationEvalDown

instance _root_.Submission.SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairChainComplexMapHomSSetOfNatHomChainComplexObjIdLeftRightEvalDown (R : C) (P : SSetPair.{w}) (n : ℕ) :
    _root_.CategoryTheory.Limits.PreservesColimit (_root_.CategoryTheory.Limits.parallelPair (SSet.chainComplexMap P.hom R) 0)
      (HomologicalComplex.eval C _ n) :=
  HomologicalComplex.eval_preservesColimit_of_hasCokernel_f ..

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairChainComplexMapHomSSetOfNatHomChainComplexObjIdLeftRightEvalDown then
    throwError "Refusing to shadow existing declaration SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairChainComplexMapHomSSetOfNatHomChainComplexObjIdLeftRightEvalDown"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairChainComplexMapHomSSetOfNatHomChainComplexObjIdLeftRightEvalDown ``Submission.SSetPair.instPreservesColimitChainComplexNatWalkingParallelPairParallelPairChainComplexMapHomSSetOfNatHomChainComplexObjIdLeftRightEvalDown

variable {C} (P P' P'' : SSetPair.{w}) (f : P ⟶ P') (g : P' ⟶ P'') (R : C)

/-- The relative chain complex of a pair `P` of simplicial sets
with coefficients in `R : C` (e.g. `C := Ab` and `R := ℤ`.)
This identifies to the cokernel of the morphism
`P.left.chainComplex R ⟶ P.right.chainComplex R` of simplicial
chain complexes. -/
noncomputable abbrev chainComplex : ChainComplex C ℕ :=
  ((SSetPair.chainComplexFunctor C).obj R).obj P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplex then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplex ``Submission.SSetPair.chainComplex

variable {P P'} in
/-- The morphism of relative simplicial chain complexes induces by a morphism
of pairs of simplicial sets. -/
noncomputable abbrev chainComplexMap : P.chainComplex R ⟶ P'.chainComplex R :=
  ((SSetPair.chainComplexFunctor C).obj R).map f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexMap then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexMap"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexMap ``Submission.SSetPair.chainComplexMap

/-- Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism),
this is the morphism from the chain complex of `Y` to the
chain complex of the pair. -/
noncomputable def chainComplexπ : P.right.chainComplex R ⟶ P.chainComplex R :=
  ((chainComplexFunctorπ.{w} C).app R).app P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexπ then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexπ ``Submission.SSetPair.chainComplexπ

@[reassoc (attr := simp)]
lemma chainComplex_condition :
    SSet.chainComplexMap P.hom R ≫ P.chainComplexπ R = 0 :=
  NatTrans.congr_app (NatTrans.congr_app (chainComplexFunctor_condition C) R) P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplex_condition then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplex_condition"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplex_condition ``Submission.SSetPair.chainComplex_condition

@[reassoc (attr := simp)]
lemma chainComplex_condition_f (n : ℕ) :
    (SSet.chainComplexMap P.hom R).f n ≫ (P.chainComplexπ R).f n = 0 := by
  simp [← HomologicalComplex.comp_f]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplex_condition_f then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplex_condition_f"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplex_condition_f ``Submission.SSetPair.chainComplex_condition_f

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and `R : C` (e.g. `C := Ab` and `R := ℤ`), this is the cokernel cofork
expressing the chain complex `SSetPair.chainComplex` of the pair
as a cokernel of the map `X.chainComplex R ⟶ Y.chainComplex R`.
-/
noncomputable def cokernelCoforkChainComplex :
    CokernelCofork (SSet.chainComplexMap P.hom R) :=
  CokernelCofork.ofπ _ (chainComplex_condition ..)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.cokernelCoforkChainComplex then
    throwError "Refusing to shadow existing declaration SSetPair.cokernelCoforkChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.cokernelCoforkChainComplex ``Submission.SSetPair.cokernelCoforkChainComplex

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism)
and `R : C` (e.g. `C := Ab` and `R := ℤ`), the chain complex
`SSetPair.chainComplex` of the pair is a cokernel of the map
`X.chainComplex R ⟶ Y.chainComplex R`.
-/
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplex :
    IsColimit (P.cokernelCoforkChainComplex R) :=
  (CokernelCofork.isColimitMapCoconeEquiv
      (cokernelCoforkChainComplexFunctorLeftToRight C)
      ((_root_.CategoryTheory.evaluation ..).obj R ⋙ (_root_.CategoryTheory.evaluation ..).obj P)).1
      (_root_.CategoryTheory.Limits.isColimitOfPreserves ((_root_.CategoryTheory.evaluation ..).obj R ⋙ (_root_.CategoryTheory.evaluation ..).obj P)
    (isColimitCokernelCoforkChainComplexFunctorLeftToRight.{w} C))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.isColimitCokernelCoforkChainComplex then
    throwError "Refusing to shadow existing declaration SSetPair.isColimitCokernelCoforkChainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.isColimitCokernelCoforkChainComplex ``Submission.SSetPair.isColimitCokernelCoforkChainComplex

instance _root_.Submission.SSetPair.instEpiChainComplexNatChainComplexπ : _root_.CategoryTheory.Epi (P.chainComplexπ R) :=
  Cofork.IsColimit.epi (P.isColimitCokernelCoforkChainComplex R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instEpiChainComplexNatChainComplexπ then
    throwError "Refusing to shadow existing declaration SSetPair.instEpiChainComplexNatChainComplexπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instEpiChainComplexNatChainComplexπ ``Submission.SSetPair.instEpiChainComplexNatChainComplexπ

instance isIso_chainComplexπ [P.left.HasDimensionLT 0] : _root_.CategoryTheory.IsIso (P.chainComplexπ R) :=
  CokernelCofork.IsColimit.isIso_π _ (P.isColimitCokernelCoforkChainComplex R) (
    (P.left.isZero_chainComplex _).eq_of_src ..)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.isIso_chainComplexπ then
    throwError "Refusing to shadow existing declaration SSetPair.isIso_chainComplexπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.isIso_chainComplexπ ``Submission.SSetPair.isIso_chainComplexπ

lemma isZero_chainComplex [_root_.CategoryTheory.IsIso P.hom] : _root_.CategoryTheory.Limits.IsZero (P.chainComplex R) := by
  simp [IsZero.iff_id_eq_zero, ← _root_.CategoryTheory.cancel_epi (P.chainComplexπ R),
    ← dsimp% _root_.CategoryTheory.cancel_epi (SSet.chainComplexMap P.hom R)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.isZero_chainComplex then
    throwError "Refusing to shadow existing declaration SSetPair.isZero_chainComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.isZero_chainComplex ``Submission.SSetPair.isZero_chainComplex

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism),
`R : C` (e.g. `C := Ab` and `R := ℤ`) and `n : ℕ`, this is the cokernel cofork
expressing the chain complex `SSetPair.chainComplex` of the pair
in degree `n` as a cokernel of the
map `(X.chainComplex R).X n ⟶ (Y.chainComplex R).X n`.
-/
noncomputable def cokernelCoforkChainComplexX (n : ℕ) :
    CokernelCofork ((SSet.chainComplexMap P.hom R).f n) :=
  CokernelCofork.ofπ _ (chainComplex_condition_f ..)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.cokernelCoforkChainComplexX then
    throwError "Refusing to shadow existing declaration SSetPair.cokernelCoforkChainComplexX"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.cokernelCoforkChainComplexX ``Submission.SSetPair.cokernelCoforkChainComplexX

/--
Given a pair of simplicial sets `i : X ⟶ Y` (with `i` a monomorphism),
`R : C` (e.g. `C := Ab` and `R := ℤ`) and `n : ℕ`,
the chain complex `SSetPair.chainComplex` of the pair in degree `n`
is a cokernel of the map `(X.chainComplex R).X n ⟶ (Y.chainComplex R).X n`.
-/
@[no_expose]
noncomputable def isColimitCokernelCoforkChainComplexX (n : ℕ) :
    IsColimit (P.cokernelCoforkChainComplexX R n) :=
  CokernelCofork.mapIsColimit _ (P.isColimitCokernelCoforkChainComplex R)
    (HomologicalComplex.eval _ _ n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.isColimitCokernelCoforkChainComplexX then
    throwError "Refusing to shadow existing declaration SSetPair.isColimitCokernelCoforkChainComplexX"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.isColimitCokernelCoforkChainComplexX ``Submission.SSetPair.isColimitCokernelCoforkChainComplexX

instance _root_.Submission.SSetPair.instEpiFNatChainComplexπ (n : ℕ) : _root_.CategoryTheory.Epi ((P.chainComplexπ R).f n) :=
  Cofork.IsColimit.epi (P.isColimitCokernelCoforkChainComplexX R n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instEpiFNatChainComplexπ then
    throwError "Refusing to shadow existing declaration SSetPair.instEpiFNatChainComplexπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instEpiFNatChainComplexπ ``Submission.SSetPair.instEpiFNatChainComplexπ

/-- Given a pair of simplicial sets corresponding to a monomorphism `i : X ⟶ Y`,
this is the (short exact) short complex which relates
the chain complex of `X`, of `Y` and of the pair. -/
noncomputable abbrev chainComplexShortComplex : _root_.CategoryTheory.ShortComplex (ChainComplex C ℕ) :=
    ShortComplex.mk _ _ (P.chainComplex_condition R)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.chainComplexShortComplex then
    throwError "Refusing to shadow existing declaration SSetPair.chainComplexShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.chainComplexShortComplex ``Submission.SSetPair.chainComplexShortComplex

section

variable [CategoryWithHomology C]

/-- The relative simplicial homology with coefficients in `R : C` in degree `n`
of a pair of simplicial sets. -/
protected noncomputable abbrev homology (n : ℕ) : C := (P.chainComplex R).homology n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homology then
    throwError "Refusing to shadow existing declaration SSetPair.homology"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homology ``Submission.SSetPair.homology

variable {P P'} in
/-- The morphism in relative simplicial homology that is induced by a morphism
of pairs of simplicial sets. -/
protected noncomputable abbrev homologyMap (n : ℕ) : P.homology R n ⟶ P'.homology R n :=
  HomologicalComplex.homologyMap (chainComplexMap f R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyMap then
    throwError "Refusing to shadow existing declaration SSetPair.homologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyMap ``Submission.SSetPair.homologyMap

@[simp]
lemma homologyMap_id (n : ℕ) : SSetPair.homologyMap (𝟙 P) R n = 𝟙 _ := by
  simp [SSetPair.homologyMap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyMap_id then
    throwError "Refusing to shadow existing declaration SSetPair.homologyMap_id"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyMap_id ``Submission.SSetPair.homologyMap_id

variable {P P' P''} in
@[reassoc]
lemma homologyMap_comp (n : ℕ) :
    SSetPair.homologyMap (f ≫ g) R n =
      SSetPair.homologyMap f R n ≫ SSetPair.homologyMap g R n := by
  simp [SSetPair.homologyMap, HomologicalComplex.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyMap_comp then
    throwError "Refusing to shadow existing declaration SSetPair.homologyMap_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyMap_comp ``Submission.SSetPair.homologyMap_comp

attribute [local simp] homologyMap_comp in
/-- The relative simplicial homology functor in degree `n` with coefficients in `R : C`. -/
@[implicit_reducible, simps]
noncomputable def homologyFunctor (n : ℕ) : SSetPair.{w} ⥤ C where
  obj P := P.homology R n
  map f := SSetPair.homologyMap f R n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyFunctor then
    throwError "Refusing to shadow existing declaration SSetPair.homologyFunctor"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyFunctor ``Submission.SSetPair.homologyFunctor

/-- Given a pair of simplicial sets corresponding to a monomorphism `i : X ⟶ Y`,
this is the morphism from the homology of `Y` to the relative homology of the pair. -/
noncomputable abbrev homologyπ (n : ℕ) : P.right.homology R n ⟶ P.homology R n :=
  HomologicalComplex.homologyMap (P.chainComplexπ R) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyπ then
    throwError "Refusing to shadow existing declaration SSetPair.homologyπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyπ ``Submission.SSetPair.homologyπ

@[reassoc (attr := simp)]
lemma homologyMap_hom_homologyπ (n : ℕ) :
    SSet.homologyMap P.hom R n ≫ P.homologyπ R n = 0 := by
  simp [← HomologicalComplex.homologyMap_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyMap_hom_homologyπ then
    throwError "Refusing to shadow existing declaration SSetPair.homologyMap_hom_homologyπ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyMap_hom_homologyπ ``Submission.SSetPair.homologyMap_hom_homologyπ

end

end

section

variable {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A]
  (P : SSetPair.{w}) (R : A)

lemma shortExact_chainComplexShortComplex :
    (P.chainComplexShortComplex R).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _
    (isColimitCokernelCoforkChainComplex ..)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.shortExact_chainComplexShortComplex then
    throwError "Refusing to shadow existing declaration SSetPair.shortExact_chainComplexShortComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.shortExact_chainComplexShortComplex ``Submission.SSetPair.shortExact_chainComplexShortComplex

/-- Given a pair of simplicial sets corresponding to a monomorphism `i : X ⟶ Y`,
this is the connecting morphism from the homology of the pair to the homology of `X`. -/
noncomputable def homologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.homology R n ⟶ P.left.homology R m :=
  (P.shortExact_chainComplexShortComplex R).δ n m (by simpa)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyδ then
    throwError "Refusing to shadow existing declaration SSetPair.homologyδ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyδ ``Submission.SSetPair.homologyδ

@[reassoc (attr := simp)]
lemma homologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    P.homologyδ R n m h ≫ SSet.homologyMap P.hom R m = 0 :=
  (P.shortExact_chainComplexShortComplex R).δ_comp n m (by simpa)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homologyδ_comp then
    throwError "Refusing to shadow existing declaration SSetPair.homologyδ_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homologyδ_comp ``Submission.SSetPair.homologyδ_comp

@[reassoc (attr := simp)]
lemma comp_homologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.homologyπ R n ≫ P.homologyδ R n m h = 0 :=
  (P.shortExact_chainComplexShortComplex R).comp_δ n m (by simpa)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.comp_homologyδ then
    throwError "Refusing to shadow existing declaration SSetPair.comp_homologyδ"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.comp_homologyδ ``Submission.SSetPair.comp_homologyδ

/-- Given `P : SSetPair` corresponding to a monomorphism `i : Y ⟶ X`,
the sequence `Hₘ₊₁(X;Y) ⟶ Hₘ(Y) ⟶ Hₘ(X)` is exact. -/
lemma homology_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.homologyδ_comp R n m h)).Exact :=
  (P.shortExact_chainComplexShortComplex R).homology_exact₁ n m h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homology_exact₁ then
    throwError "Refusing to shadow existing declaration SSetPair.homology_exact₁"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homology_exact₁ ``Submission.SSetPair.homology_exact₁

/-- Given `P : SSetPair` corresponding to a monomorphism `i : Y ⟶ X`,
the sequence `Hₙ(Y) ⟶ Hₙ(X) ⟶ Hₙ(X;Y)` is exact. -/
lemma homology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (P.homologyMap_hom_homologyπ R n)).Exact :=
  (P.shortExact_chainComplexShortComplex R).homology_exact₂ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homology_exact₂ then
    throwError "Refusing to shadow existing declaration SSetPair.homology_exact₂"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homology_exact₂ ``Submission.SSetPair.homology_exact₂

/-- Given `P : SSetPair` corresponding to a monomorphism `i : Y ⟶ X`,
the sequence `Hₘ₊₁(X) ⟶ Hₘ₊₁(X;Y) ⟶ Hₘ(Y)` is exact. -/
lemma homology_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.comp_homologyδ R n m h)).Exact :=
  (P.shortExact_chainComplexShortComplex R).homology_exact₃ n m h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.homology_exact₃ then
    throwError "Refusing to shadow existing declaration SSetPair.homology_exact₃"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.homology_exact₃ ``Submission.SSetPair.homology_exact₃

instance _root_.Submission.SSetPair.instEpiHomologyπOfNatNat : _root_.CategoryTheory.Epi (P.homologyπ R 0) :=
  HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `SSetPair.instEpiHomologyπOfNatNat then
    throwError "Refusing to shadow existing declaration SSetPair.instEpiHomologyπOfNatNat"
  Lean.modifyEnv fun env => Lean.addAlias env `SSetPair.instEpiHomologyπOfNatNat ``Submission.SSetPair.instEpiHomologyπOfNatNat

end

end SSetPair
