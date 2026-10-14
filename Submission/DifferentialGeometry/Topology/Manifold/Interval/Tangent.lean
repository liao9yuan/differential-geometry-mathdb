import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Manifold _root_.Bundle
open scoped _root_.ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.Interval

variable {a b : ℝ} [Fact (a < b)]

def tangentCoordinateIcc (z : _root_.Set.Icc a b) : TangentSpace (𝓡∂ 1) z ≃L[ℝ] ℝ := by
  let _ : FiniteDimensional ℝ (TangentSpace (𝓡∂ 1) z) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 1)))
  let _ : T2Space (TangentSpace (𝓡∂ 1) z) :=
    inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin 1)))
  let L : TangentSpace (𝓡∂ 1) z →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (z : ℝ)).toContinuousLinearMap.comp
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : _root_.Set.Icc a b → ℝ) z)
  have hs : _root_.Function.Surjective L := by
    intro y
    refine ⟨y • (1 : TangentSpace (𝓡∂ 1) z), ?_⟩
    rw [map_smul]
    have hone : L 1 = 1 := by
      dsimp only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [mfderiv_subtypeVal_Icc_one]
      rfl
    rw [hone]
    exact mul_one y
  have hd : Module.finrank ℝ (TangentSpace (𝓡∂ 1) z) = Module.finrank ℝ ℝ := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ ℝ
    simp
  have hi : _root_.Function.Injective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr hs
  exact (LinearEquiv.ofBijective L.toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc ``Submission.DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc


theorem tangentCoordinateIcc_apply (z : _root_.Set.Icc a b) (v : TangentSpace (𝓡∂ 1) z) :
    tangentCoordinateIcc z v = (NormedSpace.fromTangentSpace (z : ℝ))
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : _root_.Set.Icc a b → ℝ) z v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_apply ``Submission.DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_apply


theorem tangentCoordinateIcc_one (z : _root_.Set.Icc a b) : tangentCoordinateIcc z 1 = 1 := by
  rw [tangentCoordinateIcc_apply, mfderiv_subtypeVal_Icc_one]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_one ``Submission.DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_one

theorem tangentCoordinateIcc_symm_apply (z : _root_.Set.Icc a b) (r : ℝ) :
    (tangentCoordinateIcc z).symm r = r • (1 : TangentSpace (𝓡∂ 1) z) := by
  apply (tangentCoordinateIcc z).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, tangentCoordinateIcc_one]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply ``Submission.DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply


theorem contMDiff_tangentCoordinateIcc :
    ContMDiff (𝓡∂ 1).tangent 𝓘(ℝ, ℝ) ∞
      (fun p : TangentBundle (𝓡∂ 1) (_root_.Set.Icc a b) => tangentCoordinateIcc p.proj p.2) := by
  have hT := (contMDiff_subtypeVal_Icc (x := a) (y := b) (n := ∞)).contMDiff_tangentMap
    (m := ∞) (by simp)
  apply ((contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hT).congr
  intro p
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc ``Submission.DifferentialGeometry.Manifold.Interval.contMDiff_tangentCoordinateIcc

private theorem tangentCoordinateIcc_symm_one_of_lt (t : _root_.Set.Icc a b) (ht : t.val < b) :
    (tangentCoordinateIcc t).symm 1 =
      EuclideanSpace.single 0 (1 : ℝ) := by
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℝ ℝ)
  have hfun : (extChartAt (𝓡∂ 1) t : _root_.Set.Icc a b → EuclideanSpace ℝ (Fin 1)) =
      fun y : _root_.Set.Icc a b => L (y.val + -a) := by
    funext y
    rw [extChartAt_coe, Icc_chartedSpaceChartAt_of_le_top ht]
    ext i
    change y.val - a = y.val + -a
    ring
  have hder := congrArg (fun A : TangentSpace (𝓡∂ 1) t →L[ℝ] EuclideanSpace ℝ (Fin 1) =>
      A (1 : TangentSpace (𝓡∂ 1) t))
    (mfderiv_extChartAt_self (I := 𝓡∂ 1) (x := t))
  have hs : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, ℝ)
      (fun y : _root_.Set.Icc a b => y.val + -a) t :=
    ((contMDiff_subtypeVal_Icc (n := ∞)).add contMDiff_const).mdifferentiableAt (by simp)
  have heq : mfderiv (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      (extChartAt (𝓡∂ 1) t) t (1 : TangentSpace (𝓡∂ 1) t) = L 1 := by
    rw [hfun]
    erw [mfderiv_comp_apply t ((L.contMDiff (n := ∞)).mdifferentiableAt (by simp)) hs]
    erw [mfderiv_add ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
      mdifferentiableAt_const, mfderiv_const]
    erw [mfderiv_eq_fderiv, L.fderiv]
    change L (((mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : _root_.Set.Icc a b → ℝ) t :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) + 0) (1 : TangentSpace (𝓡∂ 1) t)) = L 1
    rw [add_zero]
    exact congrArg L (mfderiv_subtypeVal_Icc_one t)
  have hunit : L 1 = (1 : TangentSpace (𝓡∂ 1) t) := heq.symm.trans hder
  rw [tangentCoordinateIcc_symm_apply, one_smul]
  change (1 : TangentSpace (𝓡∂ 1) t) = _
  rw [← hunit]
  change (L 1 : EuclideanSpace ℝ (Fin 1)) = EuclideanSpace.single 0 1
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [L]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_one_of_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_one_of_lt target :: scope.openDecls } }

theorem tangentCoordinateIcc_symm_apply_of_lt (t : _root_.Set.Icc a b) (ht : t.val < b) (r : ℝ) :
    (tangentCoordinateIcc t).symm r = EuclideanSpace.single 0 r := by
  have hr : (tangentCoordinateIcc t).symm r = r • (tangentCoordinateIcc t).symm 1 := by
    simpa only [smul_eq_mul, mul_one] using (map_smul (tangentCoordinateIcc t).symm r (1 : ℝ))
  rw [hr, tangentCoordinateIcc_symm_one_of_lt t ht]
  change r • (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) = EuclideanSpace.single (0 : Fin 1) r
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply_of_lt ``Submission.DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc_symm_apply_of_lt

theorem mfderiv_subtypeVal_Icc_single_of_lt (t : _root_.Set.Icc a b) (ht : t.val < b) (r : ℝ) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : _root_.Set.Icc a b → ℝ) t
      (EuclideanSpace.single 0 r) = r := by
  rw [← tangentCoordinateIcc_symm_apply_of_lt t ht r]
  change tangentCoordinateIcc t ((tangentCoordinateIcc t).symm r) = r
  exact ContinuousLinearEquiv.apply_symm_apply _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.Interval.mfderiv_subtypeVal_Icc_single_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.Interval.mfderiv_subtypeVal_Icc_single_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.Interval.mfderiv_subtypeVal_Icc_single_of_lt ``Submission.DifferentialGeometry.Manifold.Interval.mfderiv_subtypeVal_Icc_single_of_lt

end DifferentialGeometry.Manifold.Interval
