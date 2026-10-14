/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TwoHandleModelAttachment

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Complex _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

def oneHandleCollar (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | ‖p.1‖ < 3 / 2 ∧ ((-1 - a < p.2 ∧ p.2 ≤ -1) ∨ (1 ≤ p.2 ∧ p.2 < 1 + a))}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCollar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCollar

def oneHandleInterior (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {p | (‖p.1‖ < 1 ∧ |p.2| < 1 + a) ∨ (‖p.1‖ < 3 / 2 ∧ 1 < |p.2| ∧ |p.2| < 1 + a)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior

def oneHandleCornerDomain (a : ℝ) : Set (ℝ × ℝ) :=
  _root_.Set.Ioo (-(3 / 4)) (a / 2) ×ˢ _root_.Set.Ioo (-(1 / 4)) (1 / 4)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain

noncomputable def oneHandleBottomL (q : ℝ × ℝ) : ℝ × ℝ := ((-1 - q.2) / 2, (1 - q.1) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL

def oneHandleBottomLinv (q : ℝ × ℝ) : ℝ × ℝ := (1 - 2 * q.2, -1 - 2 * q.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv

noncomputable def oneHandleTopL (q : ℝ × ℝ) : ℝ × ℝ := ((q.2 - 1) / 2, (1 - q.1) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL

def oneHandleTopLinv (q : ℝ × ℝ) : ℝ × ℝ := (1 - 2 * q.2, 1 + 2 * q.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv

noncomputable def oneHandleRimIndex (p : EuclideanSpace ℝ (Fin 2) × ℝ) : Fin 3 :=
  if p.2 < 0 then 1 else 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleRimIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleRimIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleRimIndex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleRimIndex

def oneHandleChartSource (a : ℝ) : Fin 3 → Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  ![oneHandleInterior a, cornerModelSource oneHandleBottomL (oneHandleCornerDomain a),
    cornerModelSource oneHandleTopL (oneHandleCornerDomain a)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartSource

def oneHandleChartTarget (a : ℝ) : Fin 3 → Set (EuclideanHalfSpace 3) :=
  ![slabChartTarget 1 2 (oneHandleInterior a), cornerModelTarget (oneHandleCornerDomain a),
    cornerModelTarget (oneHandleCornerDomain a)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartTarget ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartTarget

noncomputable def oneHandleChartVec :
    Fin 3 → EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3) :=
  ![slabChartVec 1 2, cornerModelVec oneHandleBottomL, cornerModelVec oneHandleTopL]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartVec

noncomputable def oneHandleChartInv :
    Fin 3 → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) × ℝ :=
  ![slabChartInv 1 2, cornerModelInv oneHandleBottomLinv, cornerModelInv oneHandleTopLinv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartInv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChartInv

theorem contDiff_oneHandleBottomL : ContDiff ℝ ∞ oneHandleBottomL :=
  ((contDiff_const.sub contDiff_snd).div_const 2).prodMk
    ((contDiff_const.sub contDiff_fst).div_const 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomL ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomL

theorem contDiff_oneHandleBottomLinv : ContDiff ℝ ∞ oneHandleBottomLinv :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd)).prodMk
    (contDiff_const.sub (contDiff_const.mul contDiff_fst))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomLinv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomLinv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomLinv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleBottomLinv

theorem contDiff_oneHandleTopL : ContDiff ℝ ∞ oneHandleTopL :=
  ((contDiff_snd.sub contDiff_const).div_const 2).prodMk
    ((contDiff_const.sub contDiff_fst).div_const 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopL then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopL"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopL ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopL

theorem contDiff_oneHandleTopLinv : ContDiff ℝ ∞ oneHandleTopLinv :=
  (contDiff_const.sub (contDiff_const.mul contDiff_snd)).prodMk
    (contDiff_const.add (contDiff_const.mul contDiff_fst))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopLinv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopLinv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopLinv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiff_oneHandleTopLinv

theorem oneHandleBottomL_Linv (q : ℝ × ℝ) : oneHandleBottomL (oneHandleBottomLinv q) = q := by
  simp only [oneHandleBottomL, oneHandleBottomLinv]
  ext <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL_Linv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL_Linv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL_Linv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomL_Linv

theorem oneHandleBottomLinv_L (q : ℝ × ℝ) : oneHandleBottomLinv (oneHandleBottomL q) = q := by
  simp only [oneHandleBottomL, oneHandleBottomLinv]
  ext <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv_L then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv_L"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv_L ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottomLinv_L

theorem oneHandleTopL_Linv (q : ℝ × ℝ) : oneHandleTopL (oneHandleTopLinv q) = q := by
  simp only [oneHandleTopL, oneHandleTopLinv]
  ext <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL_Linv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL_Linv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL_Linv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopL_Linv

theorem oneHandleTopLinv_L (q : ℝ × ℝ) : oneHandleTopLinv (oneHandleTopL q) = q := by
  simp only [oneHandleTopL, oneHandleTopLinv]
  ext <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv_L then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv_L"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv_L ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTopLinv_L

theorem oneHandleCornerDomain_norm_lt {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ q ∈ oneHandleCornerDomain a, ‖((q.1 : ℂ) + q.2 * _root_.Complex.I)‖ < 1 := by
  rintro q ⟨⟨h1, h2⟩, h3, h4⟩
  apply norm_ofReal_add_mul_I_lt_one
  have e1 : |q.1| < 3 / 4 := abs_lt.mpr ⟨h1, by linarith⟩
  have e2 : |q.2| < 1 / 4 := abs_lt.mpr ⟨h3, h4⟩
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_norm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_norm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_norm_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_norm_lt

theorem oneHandleCornerDomain_bottom_pos (a : ℝ) :
    ∀ q ∈ oneHandleCornerDomain a, 0 < (oneHandleBottomLinv q).1 := by
  rintro q ⟨-, -, h4⟩
  change 0 < 1 - 2 * q.2
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_bottom_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_bottom_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_bottom_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_bottom_pos

theorem oneHandleCornerDomain_top_pos (a : ℝ) :
    ∀ q ∈ oneHandleCornerDomain a, 0 < (oneHandleTopLinv q).1 := by
  rintro q ⟨-, -, h4⟩
  change 0 < 1 - 2 * q.2
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_top_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_top_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_top_pos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleCornerDomain_top_pos

theorem isOpen_oneHandleCornerDomain (a : ℝ) : IsOpen (oneHandleCornerDomain a) :=
  isOpen_Ioo.prod isOpen_Ioo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleCornerDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleCornerDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleCornerDomain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleCornerDomain

theorem oneHandleInterior_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ oneHandleInterior a, (p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a ↔
      0 ≤ 1 * p.2 + 2) := by
  intro p hp
  constructor
  · intro _
    rcases hp with ⟨-, h2⟩ | ⟨-, -, h3⟩
    · linarith [(abs_lt.mp h2).1]
    · linarith [(abs_lt.mp h3).1]
  · intro _
    rw [_root_.Set.mem_union, mem_closedBall_zero_prod_iff]
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · obtain ⟨h2a, h2b⟩ := abs_lt.mp h2
      by_cases hs : |p.2| ≤ 1
      · exact Or.inl ⟨h1.le, hs⟩
      · right
        refine ⟨by linarith, ?_⟩
        rcases lt_abs.mp (not_le.mp hs) with h | h
        · exact Or.inr ⟨h.le, h2b⟩
        · exact Or.inl ⟨by linarith, by linarith⟩
    · obtain ⟨h3a, h3b⟩ := abs_lt.mp h3
      right
      refine ⟨h1, ?_⟩
      rcases lt_abs.mp h2 with h | h
      · exact Or.inr ⟨h.le, h3b⟩
      · exact Or.inl ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior_mem_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleInterior_mem_iff

theorem oneHandleBottom_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ cornerModelSource oneHandleBottomL (oneHandleCornerDomain a),
      (p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a ↔
        ((oneHandleBottomL (‖p.1‖, p.2)).1 : ℂ) + (oneHandleBottomL (‖p.1‖, p.2)).2 * _root_.Complex.I ∈
          concaveQuadrant) := by
  rintro p ⟨-, ⟨h1, h2⟩, h3, h4⟩
  simp only [oneHandleBottomL] at h1 h2 h3 h4
  rw [ofReal_add_mul_I_mem_concaveQuadrant_iff, _root_.Set.mem_union, mem_closedBall_zero_prod_iff]
  simp only [oneHandleBottomL]
  constructor
  · rintro (⟨h5, -⟩ | ⟨-, ⟨-, h5⟩ | ⟨h5, -⟩⟩)
    · right
      linarith
    · left
      linarith
    · exfalso
      linarith
  · rintro (h5 | h5)
    · exact Or.inr ⟨by linarith, Or.inl ⟨by linarith, by linarith⟩⟩
    · by_cases hs : -1 ≤ p.2
      · exact Or.inl ⟨by linarith, abs_le.mpr ⟨hs, by linarith⟩⟩
      · exact Or.inr ⟨by linarith, Or.inl ⟨by linarith, by linarith⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottom_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottom_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottom_mem_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleBottom_mem_iff

theorem oneHandleTop_mem_iff {a : ℝ} (ha2 : a ≤ 1 / 2) :
    ∀ p ∈ cornerModelSource oneHandleTopL (oneHandleCornerDomain a),
      (p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a ↔
        ((oneHandleTopL (‖p.1‖, p.2)).1 : ℂ) + (oneHandleTopL (‖p.1‖, p.2)).2 * _root_.Complex.I ∈
          concaveQuadrant) := by
  rintro p ⟨-, ⟨h1, h2⟩, h3, h4⟩
  simp only [oneHandleTopL] at h1 h2 h3 h4
  rw [ofReal_add_mul_I_mem_concaveQuadrant_iff, _root_.Set.mem_union, mem_closedBall_zero_prod_iff]
  simp only [oneHandleTopL]
  constructor
  · rintro (⟨h5, -⟩ | ⟨-, ⟨-, h5⟩ | ⟨h5, -⟩⟩)
    · right
      linarith
    · exfalso
      linarith
    · left
      linarith
  · rintro (h5 | h5)
    · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩
    · by_cases hs : p.2 ≤ 1
      · exact Or.inl ⟨by linarith, abs_le.mpr ⟨by linarith, hs⟩⟩
      · exact Or.inr ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTop_mem_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTop_mem_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTop_mem_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleTop_mem_iff

theorem isOpen_oneHandleChartSource (a : ℝ) (j : Fin 3) : IsOpen (oneHandleChartSource a j) := by
  have hn : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) :=
    continuous_norm.comp continuous_fst
  have hs : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => |p.2|) :=
    continuous_abs.comp continuous_snd
  fin_cases j
  · exact ((isOpen_lt hn continuous_const).inter (isOpen_lt hs continuous_const)).union
      ((isOpen_lt hn continuous_const).inter
        ((isOpen_lt continuous_const hs).inter (isOpen_lt hs continuous_const)))
  · exact isOpen_cornerModelSource contDiff_oneHandleBottomL.continuous
      (isOpen_oneHandleCornerDomain a)
  · exact isOpen_cornerModelSource contDiff_oneHandleTopL.continuous
      (isOpen_oneHandleCornerDomain a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartSource

theorem isOpen_oneHandleChartTarget (a : ℝ) (j : Fin 3) : IsOpen (oneHandleChartTarget a j) := by
  fin_cases j
  · exact isOpen_slabChartTarget 1 2 (isOpen_oneHandleChartSource a 0)
  · exact isOpen_cornerModelTarget (isOpen_oneHandleCornerDomain a)
  · exact isOpen_cornerModelTarget (isOpen_oneHandleCornerDomain a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartTarget then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartTarget"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartTarget ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOpen_oneHandleChartTarget

theorem oneHandleChart_mem {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a →
      0 ≤ oneHandleChartVec j p 0 ∧
        toHalfSpace (oneHandleChartVec j p) ∈ oneHandleChartTarget a j := by
  fin_cases j
  · exact slabChart_mem (by norm_num) (oneHandleInterior_mem_iff ha2)
  · exact cornerModel_mem (oneHandleCornerDomain_norm_lt ha2) (oneHandleBottom_mem_iff ha2)
  · exact cornerModel_mem (oneHandleCornerDomain_norm_lt ha2) (oneHandleTop_mem_iff ha2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_mem

theorem oneHandleChart_inv_mem {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ y ∈ oneHandleChartTarget a j, oneHandleChartInv j y.val ∈ oneHandleChartSource a j ∧
      oneHandleChartInv j y.val ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a := by
  fin_cases j
  · exact slabChart_inv_mem (by norm_num) (oneHandleInterior_mem_iff ha2)
  · exact cornerModel_inv_mem oneHandleBottomL_Linv (oneHandleCornerDomain_bottom_pos a)
      (oneHandleBottom_mem_iff ha2)
  · exact cornerModel_inv_mem oneHandleTopL_Linv (oneHandleCornerDomain_top_pos a)
      (oneHandleTop_mem_iff ha2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_inv_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_inv_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_inv_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_inv_mem

theorem oneHandleChart_left {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a →
      oneHandleChartInv j (oneHandleChartVec j p) = p := by
  fin_cases j
  · exact fun p _ _ => slabChartInv_vec (by norm_num) 2 p
  · exact cornerModel_left oneHandleBottomLinv_L (oneHandleCornerDomain_norm_lt ha2)
      (oneHandleBottom_mem_iff ha2)
  · exact cornerModel_left oneHandleTopLinv_L (oneHandleCornerDomain_norm_lt ha2)
      (oneHandleTop_mem_iff ha2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_left

theorem oneHandleChart_right (a : ℝ) (j : Fin 3) :
    ∀ y ∈ oneHandleChartTarget a j, oneHandleChartVec j (oneHandleChartInv j y.val) = y.val := by
  fin_cases j
  · exact fun y _ => slabChartVec_inv (by norm_num) 2 y.val
  · exact cornerModel_right oneHandleBottomL_Linv (oneHandleCornerDomain_bottom_pos a)
  · exact cornerModel_right oneHandleTopL_Linv (oneHandleCornerDomain_top_pos a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_right ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_right

theorem continuousOn_oneHandleChartVec {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ContinuousOn (oneHandleChartVec j)
      (oneHandleChartSource a j ∩ (Metric.closedBall 0 1 ∪ oneHandleCollar a)) := by
  fin_cases j
  · exact (contDiff_slabChartVec 1 2).continuous.continuousOn
  · exact continuousOn_cornerModelVec contDiff_oneHandleBottomL.continuous
      (oneHandleBottom_mem_iff ha2)
  · exact continuousOn_cornerModelVec contDiff_oneHandleTopL.continuous
      (oneHandleTop_mem_iff ha2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartVec

theorem continuousOn_oneHandleChartInv (a : ℝ) (j : Fin 3) :
    ContinuousOn (fun y : EuclideanHalfSpace 3 => oneHandleChartInv j y.val)
      (oneHandleChartTarget a j) := by
  fin_cases j
  · exact ((contDiff_slabChartInv 1 2).continuous.comp continuous_subtype_val).continuousOn
  · exact continuousOn_cornerModelInv contDiff_oneHandleBottomLinv.continuous _
  · exact continuousOn_cornerModelInv contDiff_oneHandleTopLinv.continuous _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartInv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_oneHandleChartInv

theorem mem_twoHandleRim_of_eq_oneHandleBottomLinv {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : (‖p.1‖, p.2) = oneHandleBottomLinv 0) : p ∈ twoHandleRim := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [oneHandleBottomLinv, Prod.fst_zero, Prod.snd_zero] at h1 h2
  refine ⟨by linarith, ?_⟩
  rw [h2]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleBottomLinv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleBottomLinv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleBottomLinv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleBottomLinv

theorem mem_twoHandleRim_of_eq_oneHandleTopLinv {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (h : (‖p.1‖, p.2) = oneHandleTopLinv 0) : p ∈ twoHandleRim := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [oneHandleTopLinv, Prod.fst_zero, Prod.snd_zero] at h1 h2
  refine ⟨by linarith, ?_⟩
  rw [h2]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleTopLinv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleTopLinv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleTopLinv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_twoHandleRim_of_eq_oneHandleTopLinv

theorem contMDiffAt_oneHandleChartInv (a : ℝ) (j : Fin 3) :
    ∀ y ∈ oneHandleChartTarget a j, oneHandleChartInv j y.val ∉ twoHandleRim →
      ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
        (fun y : EuclideanHalfSpace 3 => oneHandleChartInv j y.val) y := by
  fin_cases j
  · exact fun y _ _ => contMDiffAt_slabChartInv 1 2 y
  · intro y hy hne
    exact contMDiffAt_cornerModelInv contDiff_oneHandleBottomLinv
      (oneHandleCornerDomain_bottom_pos a) y hy
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleBottomLinv h)
  · intro y hy hne
    exact contMDiffAt_cornerModelInv contDiff_oneHandleTopLinv
      (oneHandleCornerDomain_top_pos a) y hy
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleTopLinv h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_oneHandleChartInv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_oneHandleChartInv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_oneHandleChartInv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contMDiffAt_oneHandleChartInv

theorem contDiffAt_oneHandleChartVec {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 ∪ oneHandleCollar a →
      p ∉ twoHandleRim → ContDiffAt ℝ ∞ (oneHandleChartVec j) p := by
  fin_cases j
  · exact fun p _ _ _ => (contDiff_slabChartVec 1 2).contDiffAt
  · intro p hp hW hne
    exact contDiffAt_cornerModelVec contDiff_oneHandleBottomL oneHandleBottomLinv_L
      (oneHandleBottom_mem_iff ha2) p hp hW
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleBottomLinv h)
  · intro p hp hW hne
    exact contDiffAt_cornerModelVec contDiff_oneHandleTopL oneHandleTopLinv_L
      (oneHandleTop_mem_iff ha2) p hp hW
      fun h => hne (mem_twoHandleRim_of_eq_oneHandleTopLinv h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_oneHandleChartVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_oneHandleChartVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_oneHandleChartVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.contDiffAt_oneHandleChartVec

theorem oneHandleChart_rim (a : ℝ) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ twoHandleRim → j = oneHandleRimIndex p := by
  fin_cases j
  · rintro p (⟨h1, -⟩ | ⟨-, h2, -⟩) ⟨h3, h4⟩
    · rw [h3] at h1
      norm_num at h1
    · rw [h4] at h2
      norm_num at h2
  · rintro p ⟨-, ⟨h1, -⟩, -⟩ ⟨-, h4⟩
    simp only [oneHandleBottomL] at h1
    have hs : p.2 < 0 := by
      rcases (abs_eq zero_le_one).mp h4 with h | h <;> linarith
    exact (if_pos hs).symm
  · rintro p ⟨-, ⟨h1, -⟩, -⟩ ⟨-, h4⟩
    simp only [oneHandleTopL] at h1
    have hs : ¬ p.2 < 0 := by
      rcases (abs_eq zero_le_one).mp h4 with h | h <;> intro hlt <;> linarith
    exact (if_neg hs).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_rim then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_rim"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_rim ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_rim

theorem oneHandleChart_cover {a : ℝ} (ha : 0 < a) {p : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hp : p ∈ Metric.closedBall 0 1) : ∃ j, p ∈ oneHandleChartSource a j := by
  obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hp
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  by_cases hw1 : ‖p.1‖ < 1
  · exact ⟨0, Or.inl ⟨hw1, by linarith⟩⟩
  have hw2 : ‖p.1‖ = 1 := le_antisymm hw (not_lt.mp hw1)
  have hne : p.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw2
    norm_num at hw2
  by_cases hs3 : p.2 < 1 / 2
  · refine ⟨1, hne, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [oneHandleBottomL, hw2] <;> linarith
  · refine ⟨2, hne, ⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [oneHandleTopL, hw2] <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_cover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_cover

theorem oneHandleChart_zero_coord_eq_zero_iff {a : ℝ} (ha2 : a ≤ 1 / 2) (j : Fin 3) :
    ∀ p ∈ oneHandleChartSource a j, p ∈ Metric.closedBall 0 1 →
      (oneHandleChartVec j p 0 = 0 ↔ ‖p.1‖ = 1) := by
  fin_cases j
  · rintro p (⟨h1, h2⟩ | ⟨-, h2, -⟩) hp
    · change 1 * p.2 + 2 = 0 ↔ _
      constructor
      · intro h
        exfalso
        have := (abs_le.mp (mem_closedBall_zero_prod_iff.mp hp).2).1
        linarith
      · intro h
        rw [h] at h1
        norm_num at h1
    · have := (mem_closedBall_zero_prod_iff.mp hp).2
      exfalso
      linarith
  · intro p hp hpb
    have hQ := (oneHandleBottom_mem_iff ha2 p hp).mp (Or.inl hpb)
    obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨hs1, -⟩ := abs_le.mp hs
    change cornerChartVec (oneHandleBottomL (‖p.1‖, p.2)).1 (oneHandleBottomL (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1) 0 = 0 ↔ _
    rw [cornerChartVec_zero_coord_eq_zero_iff hQ]
    simp only [oneHandleBottomL]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩
  · intro p hp hpb
    have hQ := (oneHandleTop_mem_iff ha2 p hp).mp (Or.inl hpb)
    obtain ⟨hw, hs⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨-, hs2⟩ := abs_le.mp hs
    change cornerChartVec (oneHandleTopL (‖p.1‖, p.2)).1 (oneHandleTopL (‖p.1‖, p.2)).2
      (‖p.1‖⁻¹ • p.1) 0 = 0 ↔ _
    rw [cornerChartVec_zero_coord_eq_zero_iff hQ]
    simp only [oneHandleTopL]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · intro h
      exact Or.inr ⟨by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_zero_coord_eq_zero_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_zero_coord_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_zero_coord_eq_zero_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.oneHandleChart_zero_coord_eq_zero_iff

theorem isSmoothHandleStage_adjunction_of_oneHandleCollar
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    {A P : Type} [TopologicalSpace A] [TopologicalSpace P] [CompactSpace A] [CompactSpace P]
    [T2Space P] {i : A → P} (hi : _root_.Topology.IsClosedEmbedding i) {ψ : A → M} (hψ : _root_.Topology.IsClosedEmbedding ψ)
    {Ext : P → EuclideanSpace ℝ (Fin 2) × ℝ} (hExt : _root_.Topology.IsClosedEmbedding Ext)
    (hExtr : _root_.Set.range Ext = Metric.closedBall 0 1) (hExti : ∀ b, |(Ext b).2| = 1 ↔ b ∈ _root_.Set.range i)
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) {V : Set M} (hV : IsOpen V)
    {θ : M → EuclideanSpace ℝ (Fin 2) × ℝ} {Θ : EuclideanSpace ℝ (Fin 2) × ℝ → M}
    (hθV : _root_.Set.MapsTo θ V (oneHandleCollar a)) (hΘO : _root_.Set.MapsTo Θ (oneHandleCollar a) V)
    (hΘθ : ∀ m ∈ V, Θ (θ m) = m) (hθΘ : ∀ p ∈ oneHandleCollar a, θ (Θ p) = p)
    (hΘi : ∀ z, Θ (Ext (i z)) = ψ z)
    (hθs : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ θ V)
    (hΘs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (𝓡∂ 3) ∞ Θ (oneHandleCollar a)) :
    IsSmoothHandleStage (AdjunctionSpace i ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \ _root_.Set.range ψ) ∪
        adjunctionCell i ψ '' {b | ‖(Ext b).1‖ = 1}) := by
  have hExtball : ∀ b, Ext b ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2) × ℝ) 1 :=
    fun b => hExtr ▸ _root_.Set.mem_range_self b
  have hWeq : _root_.Set.range Ext ∪ oneHandleCollar a = Metric.closedBall 0 1 ∪ oneHandleCollar a := by
    rw [hExtr]
  refine isSmoothHandleStage_adjunction_of_modelCharts hi hψ hExt ?_ ?_ ?_ hV hθV hΘO hΘθ hθΘ
    hΘi hθs hΘs (oneHandleChartSource a) (isOpen_oneHandleChartSource a)
    (oneHandleChartTarget a) (isOpen_oneHandleChartTarget a) oneHandleChartVec oneHandleChartInv
    ?_ ?_ ?_ (oneHandleChart_right a) ?_ (continuousOn_oneHandleChartInv a) (Rim := twoHandleRim)
    ?_ (contMDiffAt_oneHandleChartInv a) ?_ oneHandleRimIndex (oneHandleChart_rim a) ?_ ?_
  · rintro p ⟨-, hp⟩ ⟨b, rfl⟩
    have h1 := (abs_le.mp (mem_closedBall_zero_prod_iff.mp (hExtball b)).2)
    have h2 : |(Ext b).2| = 1 := by
      rcases hp with ⟨-, h⟩ | ⟨h, -⟩
      · rw [abs_of_neg (by linarith)]
        linarith
      · rw [abs_of_pos (by linarith)]
        linarith
    obtain ⟨z, rfl⟩ := (hExti b).mp h2
    exact ⟨z, rfl⟩
  · intro z
    have h1 : |(Ext (i z)).2| = 1 := (hExti _).mpr ⟨z, rfl⟩
    have h2 := (mem_closedBall_zero_prod_iff.mp (hExtball (i z))).1
    refine ⟨by linarith, ?_⟩
    rcases (abs_eq zero_le_one).mp h1 with h | h
    · exact Or.inr ⟨h.ge, by linarith⟩
    · exact Or.inl ⟨by linarith, h.le⟩
  · rw [hExtr]
    rintro p ⟨hpc, hpb⟩
    have hn : Continuous (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => ‖p.1‖) :=
      continuous_norm.comp continuous_fst
    have hcl : IsClosed {p : EuclideanSpace ℝ (Fin 2) × ℝ | ‖p.1‖ ≤ 3 / 2 ∧
        ((-1 - a ≤ p.2 ∧ p.2 ≤ -1) ∨ (1 ≤ p.2 ∧ p.2 ≤ 1 + a))} :=
      (isClosed_le hn continuous_const).inter
        (((isClosed_le continuous_const continuous_snd).inter
          (isClosed_le continuous_snd continuous_const)).union
          ((isClosed_le continuous_const continuous_snd).inter
            (isClosed_le continuous_snd continuous_const)))
    have hsub : closure (oneHandleCollar a) ⊆ {p : EuclideanSpace ℝ (Fin 2) × ℝ |
        ‖p.1‖ ≤ 3 / 2 ∧ ((-1 - a ≤ p.2 ∧ p.2 ≤ -1) ∨ (1 ≤ p.2 ∧ p.2 ≤ 1 + a))} := by
      refine closure_minimal (fun q hq => ⟨hq.1.le, ?_⟩) hcl
      rcases hq.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.le, h2⟩
      · exact Or.inr ⟨h1, h2.le⟩
    obtain ⟨-, h1⟩ := hsub hpc
    obtain ⟨h3, h4⟩ := mem_closedBall_zero_prod_iff.mp hpb
    obtain ⟨h4a, h4b⟩ := abs_le.mp h4
    refine ⟨by linarith, ?_⟩
    rcases h1 with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inl ⟨by linarith, h⟩
    · exact Or.inr ⟨h, by linarith⟩
  · rw [hWeq]
    exact oneHandleChart_mem ha2
  · rw [hWeq]
    exact oneHandleChart_inv_mem ha2
  · rw [hWeq]
    exact oneHandleChart_left ha2
  · rw [hWeq]
    exact continuousOn_oneHandleChartVec ha2
  · rw [hExtr]
    intro p hp
    exact mem_closedBall_zero_prod_iff.mpr ⟨hp.1.le, hp.2.le⟩
  · rw [hWeq]
    exact contDiffAt_oneHandleChartVec ha2
  · intro b
    exact oneHandleChart_cover ha (hExtball b)
  · intro j b hj
    exact oneHandleChart_zero_coord_eq_zero_iff ha2 j (Ext b) hj (hExtball b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_of_oneHandleCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_of_oneHandleCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_of_oneHandleCollar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isSmoothHandleStage_adjunction_of_oneHandleCollar

end DifferentialGeometry.Topology.PiecewiseLinear
