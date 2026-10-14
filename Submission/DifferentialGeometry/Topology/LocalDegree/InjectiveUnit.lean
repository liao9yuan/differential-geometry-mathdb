/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.InjectiveRelativeIso
import Submission.DifferentialGeometry.Topology.LocalDegree.InjectiveOrientationCharacter

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.LocalDegree

open _root_.Submission.DifferentialGeometry.Homology

variable {d : ℕ}

theorem euclideanLocalDegree_isUnit_of_isolatingRadius_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ}
    (hR : IsolatingRadius f x R) (hinj : _root_.Set.InjOn f (_root_.Metric.ball x R)) :
    IsUnit (euclideanLocalDegree f x ⟨R, hR⟩) := by
  classical
  obtain ⟨i, hi⟩ := exists_relativeHomologyIso_of_isolatingRadius_injOn hR hinj
  let A := relativeHomology (TopCat.of (_root_.Metric.ball x R))
    ({(⟨x, _root_.Metric.mem_ball_self hR.pos⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R))
    (ModuleCat.of ℤ ℤ) (d + 1)
  let B := relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))
    (ModuleCat.of ℤ ℤ) (d + 1)
  let a : A ≃+ ℤ :=
    (localBallSphereHomologyIso _ x R hR.pos (ModuleCat.of ℤ ℤ) d).toLinearEquiv.toAddEquiv.trans
      (euclideanSphereTopReducedHomologyEquiv d)
  let b : B ≃+ ℤ :=
    (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).toLinearEquiv.toAddEquiv.trans
      (euclideanSphereTopReducedHomologyEquiv d)
  have ha : a (euclideanBallLocalGenerator x R hR.pos) = 1 := by
    change euclideanSphereTopReducedHomologyEquiv d
      ((localBallSphereHomologyIso _ x R hR.pos (ModuleCat.of ℤ ℤ) d).hom
        (euclideanBallLocalGenerator x R hR.pos)) = 1
    simp [euclideanBallLocalGenerator, euclideanSphereTopReducedHomologyEquiv_generator]
  have hb : b (euclideanLocalGenerator d) = 1 := by
    change euclideanSphereTopReducedHomologyEquiv d
      ((localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
        (euclideanLocalGenerator d)) = 1
    simp [euclideanLocalGenerator, euclideanSphereTopReducedHomologyEquiv_generator]
  let q : A := i.inv (euclideanLocalGenerator d)
  let m : ℤ := a q
  have hq : q = m • euclideanBallLocalGenerator x R hR.pos := by
    apply a.injective
    rw [map_zsmul, ha, smul_eq_mul, mul_one]
  have hgen := euclideanLocalDegree_relativeHomology hR
  have hmul : m * euclideanLocalDegree f x ⟨R, hR⟩ = 1 := by
    have hqi : i.hom q = euclideanLocalGenerator d := by
      exact congrArg (fun g => g (euclideanLocalGenerator d)) i.inv_hom_id
    have hqmap : hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) q =
        euclideanLocalGenerator d := hi ▸ hqi
    rw [hq, map_zsmul, hgen, smul_smul] at hqmap
    have hbm := congrArg b hqmap
    rw [map_zsmul, hb, smul_eq_mul, mul_one] at hbm
    exact hbm
  exact isUnit_iff_dvd_one.mpr ⟨m, by
    calc
      (1 : ℤ) = m * euclideanLocalDegree f x ⟨R, hR⟩ := hmul.symm
      _ = euclideanLocalDegree f x ⟨R, hR⟩ * m := mul_comm _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_isolatingRadius_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_isolatingRadius_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_isolatingRadius_injOn ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_isUnit_of_isolatingRadius_injOn

theorem euclideanLocalDegree_eq_one_or_neg_one_of_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {U : Set (EuclideanSpace ℝ (Fin (d + 1)))}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hinj : _root_.Set.InjOn f U)
    {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    euclideanLocalDegree (fun y => f y - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj hx) = 1 ∨
      euclideanLocalDegree (fun y => f y - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj hx) = -1 := by
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  have hIso := isolatingRadius_sub_of_injOn hf hinj hR hRU
  have hInj : _root_.Set.InjOn (fun y => f y - f x) (_root_.Metric.ball x R) := by
    intro y hy z hz h
    exact hinj (hRU (_root_.Metric.ball_subset_closedBall hy))
      (hRU (_root_.Metric.ball_subset_closedBall hz)) (add_right_cancel (by simpa only [sub_eq_add_neg] using h))
  exact Int.isUnit_iff.mp (euclideanLocalDegree_isUnit_of_isolatingRadius_injOn hIso hInj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_injOn ``Submission.DifferentialGeometry.LocalDegree.euclideanLocalDegree_eq_one_or_neg_one_of_injOn

end DifferentialGeometry.LocalDegree
