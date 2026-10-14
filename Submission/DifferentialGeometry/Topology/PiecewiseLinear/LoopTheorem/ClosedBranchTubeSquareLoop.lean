/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ClosedBranchOrientability
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ClosedBranchTubeChain

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable def spliceSquareLoop (t : ℝ) : ℝ × ℝ :=
  if t ≤ 1 / 2 then upperSpliceArc (2 * t) else lowerSpliceArc (2 - 2 * t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop

theorem spliceSquareLoop_of_le {t : ℝ} (ht : t ≤ 1 / 2) :
    spliceSquareLoop t = upperSpliceArc (2 * t) :=
  if_pos ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_le

theorem spliceSquareLoop_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) :
    spliceSquareLoop t = lowerSpliceArc (2 - 2 * t) := by
  rcases eq_or_lt_of_le ht with h | h
  · rw [← h, spliceSquareLoop_of_le le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      show (2 : ℝ) - 1 = 1 by norm_num, upperSpliceArc_one, lowerSpliceArc_one]
  · exact if_neg (not_le.mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_ge ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_of_ge

theorem continuousOn_spliceSquareLoop : ContinuousOn spliceSquareLoop (_root_.Set.Icc 0 1) := by
  have hu := isPLHomeomorphOn_upperSpliceArc.isPiecewiseAffineOn.continuousOn
  have hl := isPLHomeomorphOn_lowerSpliceArc.isPiecewiseAffineOn.continuousOn
  have hc₁ : Continuous fun t : ℝ => 2 * t := continuous_const_mul 2
  have hc₂ : Continuous fun t : ℝ => 2 - 2 * t := continuous_const.sub (continuous_const_mul 2)
  have h₁ : ContinuousOn spliceSquareLoop (_root_.Set.Icc 0 (1 / 2)) := by
    refine (hu.comp hc₁.continuousOn fun t (ht : t ∈ _root_.Set.Icc (0 : ℝ) (1 / 2)) =>
      (⟨by linarith [ht.1], by linarith [ht.2]⟩ : 2 * t ∈ _root_.Set.Icc (0 : ℝ) 1)).congr fun t ht => ?_
    exact spliceSquareLoop_of_le ht.2
  have h₂ : ContinuousOn spliceSquareLoop (_root_.Set.Icc (1 / 2) 1) := by
    refine (hl.comp hc₂.continuousOn fun t (ht : t ∈ _root_.Set.Icc (1 / 2 : ℝ) 1) =>
      (⟨by linarith [ht.2], by linarith [ht.1]⟩ : 2 - 2 * t ∈ _root_.Set.Icc (0 : ℝ) 1)).congr
        fun t ht => ?_
    exact spliceSquareLoop_of_ge ht.1
  have h := h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  rwa [_root_.Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_spliceSquareLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_spliceSquareLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_spliceSquareLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_spliceSquareLoop

theorem spliceSquareLoop_mem {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) :
    spliceSquareLoop t ∈ spliceSquareBoundary := by
  rw [← upperSpliceBoundary_union_lowerSpliceBoundary]
  rcases le_total t (1 / 2) with h | h
  · rw [spliceSquareLoop_of_le h]
    exact Or.inl (bijOn_upperSpliceArc.mapsTo ⟨by linarith [ht.1], by linarith⟩)
  · rw [spliceSquareLoop_of_ge h]
    exact Or.inr (bijOn_lowerSpliceArc.mapsTo ⟨by linarith [ht.2], by linarith⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareLoop_mem

theorem injOn_spliceSquareLoop : _root_.Set.InjOn spliceSquareLoop (_root_.Set.Ico 0 1) := by
  have hmemU : ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, upperSpliceArc s ∈ upperSpliceBoundary :=
    fun s hs => bijOn_upperSpliceArc.mapsTo hs
  have hmemL : ∀ s ∈ _root_.Set.Icc (0 : ℝ) 1, lowerSpliceArc s ∈ lowerSpliceBoundary :=
    fun s hs => bijOn_lowerSpliceArc.mapsTo hs
  have hcross : ∀ x y : ℝ, x ∈ _root_.Set.Icc (0 : ℝ) (1 / 2) → y ∈ _root_.Set.Ioo (1 / 2 : ℝ) 1 →
      upperSpliceArc (2 * x) ≠ lowerSpliceArc (2 - 2 * y) := by
    intro x y hx hy hxy
    have hx' : 2 * x ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hy' : 2 - 2 * y ∈ _root_.Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hmem : upperSpliceArc (2 * x) ∈ upperSpliceBoundary ∩ lowerSpliceBoundary :=
      ⟨hmemU _ hx', hxy ▸ hmemL _ hy'⟩
    rw [upperSpliceBoundary_inter_lowerSpliceBoundary] at hmem
    rcases hmem with h | h
    · have := bijOn_lowerSpliceArc.injOn hy' ⟨le_rfl, zero_le_one⟩
        ((hxy.symm.trans h).trans lowerSpliceArc_zero.symm)
      linarith [hy.2]
    · have := bijOn_lowerSpliceArc.injOn hy' ⟨zero_le_one, le_rfl⟩
        ((hxy.symm.trans h).trans lowerSpliceArc_one.symm)
      linarith [hy.1]
  intro x hx y hy hxy
  rcases le_or_gt x (1 / 2) with hx2 | hx2 <;> rcases le_or_gt y (1 / 2) with hy2 | hy2
  · rw [spliceSquareLoop_of_le hx2, spliceSquareLoop_of_le hy2] at hxy
    have := bijOn_upperSpliceArc.injOn ⟨by linarith [hx.1], by linarith⟩
      ⟨by linarith [hy.1], by linarith⟩ hxy
    linarith
  · rw [spliceSquareLoop_of_le hx2, spliceSquareLoop_of_ge hy2.le] at hxy
    exact (hcross x y ⟨hx.1, hx2⟩ ⟨hy2, hy.2⟩ hxy).elim
  · rw [spliceSquareLoop_of_ge hx2.le, spliceSquareLoop_of_le hy2] at hxy
    exact (hcross y x ⟨hy.1, hy2⟩ ⟨hx2, hx.2⟩ hxy.symm).elim
  · rw [spliceSquareLoop_of_ge hx2.le, spliceSquareLoop_of_ge hy2.le] at hxy
    have := bijOn_lowerSpliceArc.injOn ⟨by linarith [hx.2], by linarith⟩
      ⟨by linarith [hy.2], by linarith⟩ hxy
    linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injOn_spliceSquareLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injOn_spliceSquareLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injOn_spliceSquareLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injOn_spliceSquareLoop

theorem surjOn_spliceSquareLoop : _root_.Set.SurjOn spliceSquareLoop (_root_.Set.Ico 0 1) spliceSquareBoundary := by
  intro p hp
  rw [← upperSpliceBoundary_union_lowerSpliceBoundary] at hp
  rcases hp with hp | hp
  · obtain ⟨s, hs, rfl⟩ := bijOn_upperSpliceArc.surjOn hp
    refine ⟨s / 2, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    rw [spliceSquareLoop_of_le (by linarith [hs.2]), mul_div_cancel₀ s two_ne_zero]
  · obtain ⟨s, hs, rfl⟩ := bijOn_lowerSpliceArc.surjOn hp
    rcases eq_or_lt_of_le hs.1 with h | h
    · refine ⟨0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
      rw [← h, spliceSquareLoop_of_le (by norm_num), _root_.MulZeroClass.mul_zero, upperSpliceArc_zero,
        lowerSpliceArc_zero]
    · refine ⟨1 - s / 2, ⟨by linarith [hs.2], by linarith⟩, ?_⟩
      rw [spliceSquareLoop_of_ge (by linarith [hs.2])]
      congr 1
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.surjOn_spliceSquareLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.surjOn_spliceSquareLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.surjOn_spliceSquareLoop ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjOn_spliceSquareLoop

noncomputable def spliceLeafTime : Fin 4 → ℝ
  | 0 => 0
  | 1 => 1 / 4
  | 2 => 1 / 2
  | 3 => 3 / 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime

theorem spliceLeafTime_zero : spliceLeafTime 0 = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_zero

theorem spliceLeafTime_one : spliceLeafTime 1 = 1 / 4 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_one

theorem spliceLeafTime_two : spliceLeafTime 2 = 1 / 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_two

theorem spliceLeafTime_three : spliceLeafTime 3 = 3 / 4 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceLeafTime_three

theorem exists_spliceSquare_cyclic :
    ∃ (g : loopCircle → ℝ × ℝ) (v : Fin 4 → ℝ), Continuous g ∧
      _root_.Set.BijOn g _root_.Set.univ spliceSquareBoundary ∧ v 0 < v 1 ∧ v 1 < v 2 ∧ v 2 < v 3 ∧
        v 3 < v 0 + 1 ∧ ∀ i, fourSpokeModelLeaf i = g ((v i : ℝ) : loopCircle) := by
  have h01 : spliceSquareLoop 0 = spliceSquareLoop (0 + 1) := by
    rw [spliceSquareLoop_of_le (by norm_num), zero_add, spliceSquareLoop_of_ge (by norm_num),
      _root_.MulZeroClass.mul_zero, show (2 : ℝ) - 2 * 1 = 0 by norm_num, upperSpliceArc_zero, lowerSpliceArc_zero]
  have hcont : Continuous (AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop) :=
    AddCircle.liftIco_continuous h01 (by rw [zero_add]; exact continuousOn_spliceSquareLoop)
  have happ : ∀ x ∈ _root_.Set.Ico (0 : ℝ) 1,
      AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop (x : loopCircle) = spliceSquareLoop x :=
    fun x hx => AddCircle.liftIco_coe_apply (by rwa [zero_add])
  have hval : ∀ z : loopCircle, AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop z =
      spliceSquareLoop (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) := fun _ => rfl
  have hmemIco : ∀ z : loopCircle, (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) ∈ _root_.Set.Ico (0 : ℝ) 1 :=
    fun z => by simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).2
  refine ⟨AddCircle.liftIco (1 : ℝ) 0 spliceSquareLoop, spliceLeafTime, hcont,
    ⟨fun z _ => ?_, fun z _ w _ hzw => ?_, fun p hp => ?_⟩, ?_, ?_, ?_, ?_, fun i => ?_⟩
  · rw [hval]
    exact spliceSquareLoop_mem (_root_.Set.Ico_subset_Icc_self (hmemIco z))
  · rw [hval, hval] at hzw
    exact (AddCircle.equivIco (1 : ℝ) 0).injective
      (Subtype.ext (injOn_spliceSquareLoop (hmemIco z) (hmemIco w) hzw))
  · obtain ⟨x, hx, rfl⟩ := surjOn_spliceSquareLoop hp
    exact ⟨(x : loopCircle), _root_.Set.mem_univ _, happ x hx⟩
  · rw [spliceLeafTime_zero, spliceLeafTime_one]
    norm_num
  · rw [spliceLeafTime_one, spliceLeafTime_two]
    norm_num
  · rw [spliceLeafTime_two, spliceLeafTime_three]
    norm_num
  · rw [spliceLeafTime_three, spliceLeafTime_zero]
    norm_num
  · rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
    · rw [spliceLeafTime_zero, happ 0 ⟨le_rfl, zero_lt_one⟩,
        spliceSquareLoop_of_le (by norm_num), _root_.MulZeroClass.mul_zero, upperSpliceArc_zero]
      rfl
    · rw [spliceLeafTime_one, happ (1 / 4) ⟨by norm_num, by norm_num⟩,
        spliceSquareLoop_of_le (by norm_num), upperSpliceArc_of_mem (by norm_num) (by norm_num)]
      norm_num [fourSpokeModelLeaf]
    · rw [spliceLeafTime_two, happ (1 / 2) ⟨by norm_num, by norm_num⟩,
        spliceSquareLoop_of_le le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
        upperSpliceArc_one]
      rfl
    · rw [spliceLeafTime_three, happ (3 / 4) ⟨by norm_num, by norm_num⟩,
        spliceSquareLoop_of_ge (by norm_num), lowerSpliceArc_of_mem (by norm_num) (by norm_num)]
      norm_num [fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_spliceSquare_cyclic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_spliceSquare_cyclic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_spliceSquare_cyclic ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_spliceSquare_cyclic

theorem boundaryComplex_space_of_space_eq_spliceSquare
    (Pc : Geometry.SimplicialComplex ℝ (ℝ × ℝ)) [Finite Pc.faces] (hPc : Pc.space = spliceSquare) :
    (boundaryComplex 2 Pc).space = spliceSquareBoundary := by
  classical
  have hball : IsPLBall (1 + 1) Pc.space := by
    rw [hPc]
    exact isPLBall_spliceSquare
  rw [← frontier_space_eq_boundaryComplex_space_of_finrank (n := 1) (by simp) Pc
    hball.isCombinatorialManifoldWithBoundary, hPc, spliceSquareBoundary_eq_frontier]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_space_eq_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_space_eq_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_space_eq_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_space_eq_spliceSquare

end DifferentialGeometry.Topology.PiecewiseLinear
