/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchDescent
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isHPolytope_singleton_real (a : ℝ) : IsHPolytope ({a} : Set ℝ) := by
  rw [← Set.Icc_self a]
  exact isHPolytope_Icc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_singleton_real then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_singleton_real"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_singleton_real ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isHPolytope_singleton_real

def crossRayPosX : Set (ℝ × ℝ) := _root_.Set.Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosX

def crossRayNegX : Set (ℝ × ℝ) := _root_.Set.Icc (-1 : ℝ) 0 ×ˢ ({0} : Set ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegX

def crossRayPosY : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossRayPosY

def crossRayNegY : Set (ℝ × ℝ) := ({0} : Set ℝ) ×ˢ _root_.Set.Icc (-1 : ℝ) 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossRayNegY

theorem mem_crossRayPosX {p : ℝ × ℝ} :
    p ∈ crossRayPosX ↔ (0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 = 0 := by
  simp only [crossRayPosX, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosX

theorem mem_crossRayNegX {p : ℝ × ℝ} :
    p ∈ crossRayNegX ↔ (-1 ≤ p.1 ∧ p.1 ≤ 0) ∧ p.2 = 0 := by
  simp only [crossRayNegX, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegX

theorem mem_crossRayPosY {p : ℝ × ℝ} :
    p ∈ crossRayPosY ↔ p.1 = 0 ∧ (0 ≤ p.2 ∧ p.2 ≤ 1) := by
  simp only [crossRayPosY, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayPosY

theorem mem_crossRayNegY {p : ℝ × ℝ} :
    p ∈ crossRayNegY ↔ p.1 = 0 ∧ (-1 ≤ p.2 ∧ p.2 ≤ 0) := by
  simp only [crossRayNegY, Set.mem_prod, Set.mem_Icc, Set.mem_singleton_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_crossRayNegY

theorem crossingArcY_eq_union : crossingArcY = crossRayNegX ∪ crossRayPosX := by
  rw [crossingArcY_eq, crossRayNegX, crossRayPosX, ← Set.union_prod,
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossingArcY_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossingArcY_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossingArcY_eq_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossingArcY_eq_union

theorem crossingArcX_eq_union : crossingArcX = crossRayNegY ∪ crossRayPosY := by
  rw [crossingArcX_eq, crossRayNegY, crossRayPosY, ← Set.prod_union,
    Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossingArcX_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossingArcX_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossingArcX_eq_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossingArcX_eq_union

def bentArcPos : Set (ℝ × ℝ) := crossRayPosX ∪ crossRayNegY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos

def bentArcNeg : Set (ℝ × ℝ) := crossRayNegX ∪ crossRayPosY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg

def bentSheetPos : Set ((ℝ × ℝ) × ℝ) := bentArcPos ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos

def bentSheetNeg : Set ((ℝ × ℝ) × ℝ) := bentArcNeg ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentSheetNeg

def bentFigure : Set ((ℝ × ℝ) × ℝ) := (bentArcPos ∪ bentArcNeg) ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentFigure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentFigure

theorem mem_bentArcPos {p : ℝ × ℝ} :
    p ∈ bentArcPos ↔ ((0 ≤ p.1 ∧ p.1 ≤ 1) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (-1 ≤ p.2 ∧ p.2 ≤ 0)) := by
  rw [bentArcPos, Set.mem_union, mem_crossRayPosX, mem_crossRayNegY]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcPos

theorem mem_bentArcNeg {p : ℝ × ℝ} :
    p ∈ bentArcNeg ↔ ((-1 ≤ p.1 ∧ p.1 ≤ 0) ∧ p.2 = 0) ∨ (p.1 = 0 ∧ (0 ≤ p.2 ∧ p.2 ≤ 1)) := by
  rw [bentArcNeg, Set.mem_union, mem_crossRayNegX, mem_crossRayPosY]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_bentArcNeg

theorem bentArcPos_subset_spliceSquare : bentArcPos ⊆ spliceSquare := by
  intro p hp
  rw [mem_bentArcPos] at hp
  rw [mem_spliceSquare]
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
  · exact ⟨⟨by linarith, h1⟩, by rw [h2]; norm_num⟩
  · exact ⟨by rw [h1]; norm_num, h0, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_subset_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_subset_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_subset_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_subset_spliceSquare

theorem bentArcNeg_subset_spliceSquare : bentArcNeg ⊆ spliceSquare := by
  intro p hp
  rw [mem_bentArcNeg] at hp
  rw [mem_spliceSquare]
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
  · exact ⟨⟨h0, by linarith⟩, by rw [h2]; norm_num⟩
  · exact ⟨by rw [h1]; norm_num, by linarith, h2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_subset_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_subset_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_subset_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_subset_spliceSquare

theorem bentArcPos_union_bentArcNeg :
    bentArcPos ∪ bentArcNeg = crossingArcX ∪ crossingArcY := by
  rw [bentArcPos, bentArcNeg, crossingArcX_eq_union, crossingArcY_eq_union]
  ext p
  simp only [Set.mem_union]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_union_bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_union_bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_union_bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_union_bentArcNeg

theorem bentArcPos_inter_bentArcNeg : bentArcPos ∩ bentArcNeg = {((0 : ℝ), (0 : ℝ))} := by
  apply Set.Subset.antisymm
  · rintro p ⟨hpos, hneg⟩
    rw [mem_bentArcPos] at hpos
    rw [mem_bentArcNeg] at hneg
    have h1 : p.1 = 0 := by
      rcases hpos with ⟨hp, -⟩ | ⟨hp, -⟩
      · rcases hneg with ⟨hq, -⟩ | ⟨hq, -⟩
        · linarith [hp.1, hq.2]
        · exact hq
      · exact hp
    have h2 : p.2 = 0 := by
      rcases hpos with ⟨-, hp⟩ | ⟨-, hp⟩
      · exact hp
      · rcases hneg with ⟨-, hq⟩ | ⟨-, hq⟩
        · exact hq
        · linarith [hp.2, hq.1]
    exact Prod.ext h1 h2
  · rintro p rfl
    refine ⟨mem_bentArcPos.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
      mem_bentArcNeg.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_bentArcNeg

theorem bentFigure_eq_crossingFigure : bentFigure = crossingFigure := by
  rw [bentFigure, crossingFigure, bentArcPos_union_bentArcNeg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_crossingFigure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_crossingFigure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_crossingFigure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_crossingFigure

theorem bentSheetPos_inter_bentSheetNeg : bentSheetPos ∩ bentSheetNeg = spliceCore := by
  rw [bentSheetPos, bentSheetNeg, Set.prod_inter_prod, Set.inter_self,
    bentArcPos_inter_bentArcNeg, spliceCore]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_inter_bentSheetNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_inter_bentSheetNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_inter_bentSheetNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentSheetPos_inter_bentSheetNeg

theorem bentArcPos_inter_spliceSquareBoundary :
    bentArcPos ∩ spliceSquareBoundary = {((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (-1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨harc, -, hb⟩
    rw [mem_bentArcPos] at harc
    rcases harc with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [hx] at h0; linarith)
      · exact Or.inl (Prod.ext h h2)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact Or.inr (Prod.ext h1 h)
      · exact absurd h (by intro hx; rw [hx] at h2; linarith)
  · rintro (rfl | rfl)
    · exact ⟨mem_bentArcPos.mpr (Or.inl ⟨⟨by norm_num, le_rfl⟩, rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inl rfl)⟩⟩
    · exact ⟨mem_bentArcPos.mpr (Or.inr ⟨rfl, le_rfl, by norm_num⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inl rfl))⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_spliceSquareBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_spliceSquareBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_spliceSquareBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_spliceSquareBoundary

theorem bentArcNeg_inter_spliceSquareBoundary :
    bentArcNeg ∩ spliceSquareBoundary = {((-1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))} := by
  ext p
  constructor
  · rintro ⟨harc, -, hb⟩
    rw [mem_bentArcNeg] at harc
    rcases harc with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩
    · rcases hb with h | h | h | h
      · exact Or.inl (Prod.ext h h2)
      · exact absurd h (by intro hx; rw [hx] at h1; linarith)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h2] at hx; norm_num at hx)
    · rcases hb with h | h | h | h
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [h1] at hx; norm_num at hx)
      · exact absurd h (by intro hx; rw [hx] at h0; linarith)
      · exact Or.inr (Prod.ext h1 h)
  · rintro (rfl | rfl)
    · exact ⟨mem_bentArcNeg.mpr (Or.inl ⟨⟨le_rfl, by norm_num⟩, rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inl rfl⟩⟩
    · exact ⟨mem_bentArcNeg.mpr (Or.inr ⟨rfl, by norm_num, le_rfl⟩),
        ⟨by simp only [mem_spliceSquare]; norm_num, Or.inr (Or.inr (Or.inr rfl))⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_spliceSquareBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_spliceSquareBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_spliceSquareBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_spliceSquareBoundary

theorem bentArcPos_inter_lateral_eq :
    bentArcPos ∩ spliceSquareBoundary = spliceArcPos ∩ spliceSquareBoundary := by
  rw [bentArcPos_inter_spliceSquareBoundary, spliceArcPos_inter_spliceSquareBoundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_lateral_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_lateral_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_lateral_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcPos_inter_lateral_eq

theorem bentArcNeg_inter_lateral_eq :
    bentArcNeg ∩ spliceSquareBoundary = spliceArcNeg ∩ spliceSquareBoundary := by
  rw [bentArcNeg_inter_spliceSquareBoundary, spliceArcNeg_inter_spliceSquareBoundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_lateral_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_lateral_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_lateral_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentArcNeg_inter_lateral_eq

theorem bentFigure_inter_lateral :
    bentFigure ∩ (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) = spliceEnds ×ˢ _root_.Set.Icc (0 : ℝ) 1 := by
  rw [bentFigure_eq_crossingFigure]
  exact crossingFigure_inter_lateral

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_inter_lateral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_inter_lateral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_inter_lateral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_inter_lateral

theorem isPolyhedron_bentArcPos : IsPolyhedron bentArcPos :=
  (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).isPolyhedron.union
    ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).isPolyhedron

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcPos

theorem isPolyhedron_bentArcNeg : IsPolyhedron bentArcNeg :=
  (isHPolytope_Icc.prod (isHPolytope_singleton_real 0)).isPolyhedron.union
    ((isHPolytope_singleton_real 0).prod isHPolytope_Icc).isPolyhedron

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPolyhedron_bentArcNeg

noncomputable def crossSeamChordPos (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 + 1) / 2, (p.1 + p.2 - 1) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos

noncomputable def crossSeamChordNeg (p : ℝ × ℝ) : ℝ × ℝ :=
  ((p.1 + p.2 - 1) / 2, (p.1 + p.2 + 1) / 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg

theorem crossSeamChordPos_fst (p : ℝ × ℝ) :
    (crossSeamChordPos p).1 = (p.1 + p.2 + 1) / 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_fst

theorem crossSeamChordPos_snd (p : ℝ × ℝ) :
    (crossSeamChordPos p).2 = (p.1 + p.2 - 1) / 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_snd

theorem crossSeamChordNeg_fst (p : ℝ × ℝ) :
    (crossSeamChordNeg p).1 = (p.1 + p.2 - 1) / 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_fst

theorem crossSeamChordNeg_snd (p : ℝ × ℝ) :
    (crossSeamChordNeg p).2 = (p.1 + p.2 + 1) / 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_snd

noncomputable def crossSeamChordMapPos : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun := crossSeamChordPos
  linear := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).smulRight ((1 / 2 : ℝ), (1 / 2 : ℝ))
  map_vadd' p v := by
    refine Prod.ext ?_ ?_ <;> simp [crossSeamChordPos] <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos

noncomputable def crossSeamChordMapNeg : (ℝ × ℝ) →ᵃ[ℝ] ℝ × ℝ where
  toFun := crossSeamChordNeg
  linear := (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).smulRight ((1 / 2 : ℝ), (1 / 2 : ℝ))
  map_vadd' p v := by
    refine Prod.ext ?_ ?_ <;> simp [crossSeamChordNeg] <;> ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg

theorem crossSeamChordMapPos_apply (p : ℝ × ℝ) :
    crossSeamChordMapPos p = crossSeamChordPos p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapPos_apply

theorem crossSeamChordMapNeg_apply (p : ℝ × ℝ) :
    crossSeamChordMapNeg p = crossSeamChordNeg p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordMapNeg_apply

theorem crossSeamChordPos_apply_posX : crossSeamChordPos ((1 : ℝ), (0 : ℝ)) = (1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_posX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_posX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_posX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_posX

theorem crossSeamChordPos_apply_negY : crossSeamChordPos ((0 : ℝ), (-1 : ℝ)) = (0, -1) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_negY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_negY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_negY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordPos_apply_negY

theorem crossSeamChordNeg_apply_negX : crossSeamChordNeg ((-1 : ℝ), (0 : ℝ)) = (-1, 0) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_negX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_negX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_negX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_negX

theorem crossSeamChordNeg_apply_posY : crossSeamChordNeg ((0 : ℝ), (1 : ℝ)) = (0, 1) := by
  refine Prod.ext ?_ ?_ <;> simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_posY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_posY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_posY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamChordNeg_apply_posY

theorem sum_mem_Icc_of_mem_bentArcPos {p : ℝ × ℝ} (hp : p ∈ bentArcPos) :
    -1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [mem_bentArcPos] at hp
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩ <;> constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcPos

theorem sum_mem_Icc_of_mem_bentArcNeg {p : ℝ × ℝ} (hp : p ∈ bentArcNeg) :
    -1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 1 := by
  rw [mem_bentArcNeg] at hp
  rcases hp with ⟨⟨h0, h1⟩, h2⟩ | ⟨h1, h0, h2⟩ <;> constructor <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.sum_mem_Icc_of_mem_bentArcNeg

theorem mapsTo_crossSeamChordPos : _root_.Set.MapsTo crossSeamChordPos bentArcPos spliceArcPos := by
  intro p hp
  obtain ⟨hlow, hhigh⟩ := sum_mem_Icc_of_mem_bentArcPos hp
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [crossSeamChordPos_fst]; linarith
  · rw [crossSeamChordPos_fst]; linarith
  · rw [crossSeamChordPos_snd]; linarith
  · rw [crossSeamChordPos_snd]; linarith
  · rw [crossSeamChordPos_fst, crossSeamChordPos_snd]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordPos

theorem mapsTo_crossSeamChordNeg : _root_.Set.MapsTo crossSeamChordNeg bentArcNeg spliceArcNeg := by
  intro p hp
  obtain ⟨hlow, hhigh⟩ := sum_mem_Icc_of_mem_bentArcNeg hp
  refine ⟨mem_spliceSquare.mpr ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [crossSeamChordNeg_fst]; linarith
  · rw [crossSeamChordNeg_fst]; linarith
  · rw [crossSeamChordNeg_snd]; linarith
  · rw [crossSeamChordNeg_snd]; linarith
  · rw [crossSeamChordNeg_fst, crossSeamChordNeg_snd]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_crossSeamChordNeg

theorem injOn_crossSeamChordPos : _root_.Set.InjOn crossSeamChordPos bentArcPos := by
  intro p hp q hq hpq
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    have h := congrArg Prod.fst hpq
    rw [crossSeamChordPos_fst, crossSeamChordPos_fst] at h
    linarith
  rw [mem_bentArcPos] at hp hq
  rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩ | ⟨hp1, hp0, hp2⟩ <;>
    rcases hq with ⟨⟨hq0, hq1⟩, hq2⟩ | ⟨hq1, hq0, hq2⟩ <;>
      exact Prod.ext (by linarith) (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordPos

theorem injOn_crossSeamChordNeg : _root_.Set.InjOn crossSeamChordNeg bentArcNeg := by
  intro p hp q hq hpq
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    have h := congrArg Prod.fst hpq
    rw [crossSeamChordNeg_fst, crossSeamChordNeg_fst] at h
    linarith
  rw [mem_bentArcNeg] at hp hq
  rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩ | ⟨hp1, hp0, hp2⟩ <;>
    rcases hq with ⟨⟨hq0, hq1⟩, hq2⟩ | ⟨hq1, hq0, hq2⟩ <;>
      exact Prod.ext (by linarith) (by linarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamChordNeg

theorem surjOn_crossSeamChordPos : _root_.Set.SurjOn crossSeamChordPos bentArcPos spliceArcPos := by
  rintro q ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  by_cases hs : 0 ≤ q.1 + q.2
  · refine ⟨(q.1 + q.2, 0), mem_bentArcPos.mpr (Or.inl ⟨⟨hs, ?_⟩, rfl⟩), ?_⟩
    · linarith [hsq.1.2, hsq.2.2]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> linarith
  · replace hs : q.1 + q.2 < 0 := not_le.mp hs
    refine ⟨(0, q.1 + q.2), mem_bentArcPos.mpr (Or.inr ⟨rfl, ?_, le_of_lt hs⟩), ?_⟩
    · linarith [hsq.1.1, hsq.2.1]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordPos_fst, crossSeamChordPos_snd] <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordPos

theorem surjOn_crossSeamChordNeg : _root_.Set.SurjOn crossSeamChordNeg bentArcNeg spliceArcNeg := by
  rintro q ⟨hsq, hd⟩
  rw [mem_spliceSquare] at hsq
  by_cases hs : 0 ≤ q.1 + q.2
  · refine ⟨(0, q.1 + q.2), mem_bentArcNeg.mpr (Or.inr ⟨rfl, hs, ?_⟩), ?_⟩
    · linarith [hsq.1.2, hsq.2.2]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> linarith
  · replace hs : q.1 + q.2 < 0 := not_le.mp hs
    refine ⟨(q.1 + q.2, 0), mem_bentArcNeg.mpr (Or.inl ⟨⟨?_, le_of_lt hs⟩, rfl⟩), ?_⟩
    · linarith [hsq.1.1, hsq.2.1]
    · refine Prod.ext ?_ ?_ <;>
        simp only [crossSeamChordNeg_fst, crossSeamChordNeg_snd] <;> linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.surjOn_crossSeamChordNeg

theorem bijOn_crossSeamChordPos : _root_.Set.BijOn crossSeamChordPos bentArcPos spliceArcPos :=
  ⟨mapsTo_crossSeamChordPos, injOn_crossSeamChordPos, surjOn_crossSeamChordPos⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordPos

theorem bijOn_crossSeamChordNeg : _root_.Set.BijOn crossSeamChordNeg bentArcNeg spliceArcNeg :=
  ⟨mapsTo_crossSeamChordNeg, injOn_crossSeamChordNeg, surjOn_crossSeamChordNeg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bijOn_crossSeamChordNeg

theorem isPiecewiseAffineOn_crossSeamChordPos :
    IsPiecewiseAffineOn crossSeamChordPos bentArcPos :=
  ((isPiecewiseAffineOn_of_affine_of_isHPolytope crossSeamChordMapPos
    isHPolytope_spliceSquare).mono_of_isPolyhedron isPolyhedron_bentArcPos
      bentArcPos_subset_spliceSquare).congr fun p _ => (crossSeamChordMapPos_apply p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordPos

theorem isPiecewiseAffineOn_crossSeamChordNeg :
    IsPiecewiseAffineOn crossSeamChordNeg bentArcNeg :=
  ((isPiecewiseAffineOn_of_affine_of_isHPolytope crossSeamChordMapNeg
    isHPolytope_spliceSquare).mono_of_isPolyhedron isPolyhedron_bentArcNeg
      bentArcNeg_subset_spliceSquare).congr fun p _ => (crossSeamChordMapNeg_apply p).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPiecewiseAffineOn_crossSeamChordNeg

theorem isPLHomeomorphOn_crossSeamChordPos :
    IsPLHomeomorphOn crossSeamChordPos bentArcPos spliceArcPos :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPolyhedron_bentArcPos
    isPiecewiseAffineOn_crossSeamChordPos bijOn_crossSeamChordPos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordPos

theorem isPLHomeomorphOn_crossSeamChordNeg :
    IsPLHomeomorphOn crossSeamChordNeg bentArcNeg spliceArcNeg :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isPolyhedron_bentArcNeg
    isPiecewiseAffineOn_crossSeamChordNeg bijOn_crossSeamChordNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamChordNeg

theorem spliceArcPos_eq_segment :
    spliceArcPos = segment ℝ ((0 : ℝ), (-1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
  rw [spliceArcPos_eq, segment_eq_image]
  refine Set.image_congr fun t _ => ?_
  have h : (1 - t) • ((0 : ℝ), (-1 : ℝ)) + t • ((1 : ℝ), (0 : ℝ))
      = ((1 - t) * 0 + t * 1, (1 - t) * (-1) + t * 0) := rfl
  rw [h]
  exact Prod.ext (by ring) (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceArcPos_eq_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceArcPos_eq_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceArcPos_eq_segment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceArcPos_eq_segment

theorem spliceArcNeg_eq_segment :
    spliceArcNeg = segment ℝ ((-1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) := by
  rw [spliceArcNeg_eq, segment_eq_image]
  refine Set.image_congr fun t _ => ?_
  have h : (1 - t) • ((-1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ))
      = ((1 - t) * (-1) + t * 0, (1 - t) * 0 + t * 1) := rfl
  rw [h]
  exact Prod.ext (by ring) (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceArcNeg_eq_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceArcNeg_eq_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceArcNeg_eq_segment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceArcNeg_eq_segment

theorem isPLBall_spliceArcPos : IsPLBall 1 spliceArcPos := by
  rw [spliceArcPos_eq_segment]
  refine isPLBall_segment fun h => ?_
  exact absurd (congrArg Prod.fst h) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcPos

theorem isPLBall_spliceArcNeg : IsPLBall 1 spliceArcNeg := by
  rw [spliceArcNeg_eq_segment]
  refine isPLBall_segment fun h => ?_
  exact absurd (congrArg Prod.fst h) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceArcNeg

theorem isPLBall_bentArcPos : IsPLBall 1 bentArcPos :=
  isPLBall_spliceArcPos.of_isPLHomeomorphOn isPLHomeomorphOn_crossSeamChordPos.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcPos

theorem isPLBall_bentArcNeg : IsPLBall 1 bentArcNeg :=
  isPLBall_spliceArcNeg.of_isPLHomeomorphOn isPLHomeomorphOn_crossSeamChordNeg.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentArcNeg

theorem isPLBall_bentSheetPos : IsPLBall 2 bentSheetPos :=
  isPLBall_two_prod isPLBall_bentArcPos (isPLBall_Icc zero_lt_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetPos

theorem isPLBall_bentSheetNeg : IsPLBall 2 bentSheetNeg :=
  isPLBall_two_prod isPLBall_bentArcNeg (isPLBall_Icc zero_lt_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_bentSheetNeg

theorem isPLBall_spliceSheetPos : IsPLBall 2 spliceSheetPos :=
  isPLBall_two_prod isPLBall_spliceArcPos (isPLBall_Icc zero_lt_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetPos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetPos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetPos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetPos

theorem isPLBall_spliceSheetNeg : IsPLBall 2 spliceSheetNeg :=
  isPLBall_two_prod isPLBall_spliceArcNeg (isPLBall_Icc zero_lt_one)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_spliceSheetNeg

noncomputable def crossSeamResolvePos : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map crossSeamChordPos id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos

noncomputable def crossSeamResolveNeg : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
  Prod.map crossSeamChordNeg id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg

theorem crossSeamResolvePos_fst (p : (ℝ × ℝ) × ℝ) :
    (crossSeamResolvePos p).1 = crossSeamChordPos p.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_fst

theorem crossSeamResolvePos_snd (p : (ℝ × ℝ) × ℝ) : (crossSeamResolvePos p).2 = p.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_snd

theorem crossSeamResolveNeg_fst (p : (ℝ × ℝ) × ℝ) :
    (crossSeamResolveNeg p).1 = crossSeamChordNeg p.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_fst then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_fst"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_fst ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_fst

theorem crossSeamResolveNeg_snd (p : (ℝ × ℝ) × ℝ) : (crossSeamResolveNeg p).2 = p.2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_snd

theorem isPLHomeomorphOn_crossSeamResolvePos :
    IsPLHomeomorphOn crossSeamResolvePos bentSheetPos spliceSheetPos :=
  isPLHomeomorphOn_crossSeamChordPos.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolvePos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolvePos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolvePos ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolvePos

theorem isPLHomeomorphOn_crossSeamResolveNeg :
    IsPLHomeomorphOn crossSeamResolveNeg bentSheetNeg spliceSheetNeg :=
  isPLHomeomorphOn_crossSeamChordNeg.prodMap
    (IsPolyhedron.isPLHomeomorphOn_id isHPolytope_Icc.isPolyhedron)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolveNeg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolveNeg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolveNeg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_crossSeamResolveNeg

theorem disjoint_image_crossSeamResolve :
    Disjoint (crossSeamResolvePos '' bentSheetPos) (crossSeamResolveNeg '' bentSheetNeg) := by
  rw [isPLHomeomorphOn_crossSeamResolvePos.bijOn.image_eq,
    isPLHomeomorphOn_crossSeamResolveNeg.bijOn.image_eq]
  exact disjoint_spliceSheetPos_spliceSheetNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_image_crossSeamResolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_image_crossSeamResolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_image_crossSeamResolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_image_crossSeamResolve

theorem crossSeamResolvePos_eqOn_lateral :
    EqOn crossSeamResolvePos id (bentSheetPos ∩ (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  rintro p ⟨⟨harc, -⟩, hb, -⟩
  have hp : p.1 ∈ bentArcPos ∩ spliceSquareBoundary := ⟨harc, hb⟩
  rw [bentArcPos_inter_spliceSquareBoundary] at hp
  refine Prod.ext ?_ (crossSeamResolvePos_snd p)
  rw [crossSeamResolvePos_fst]
  change crossSeamChordPos p.1 = p.1
  rcases hp with h | h
  · rw [h]; exact crossSeamChordPos_apply_posX
  · rw [Set.mem_singleton_iff.mp h]; exact crossSeamChordPos_apply_negY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_eqOn_lateral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_eqOn_lateral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_eqOn_lateral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolvePos_eqOn_lateral

theorem crossSeamResolveNeg_eqOn_lateral :
    EqOn crossSeamResolveNeg id (bentSheetNeg ∩ (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
  rintro p ⟨⟨harc, -⟩, hb, -⟩
  have hp : p.1 ∈ bentArcNeg ∩ spliceSquareBoundary := ⟨harc, hb⟩
  rw [bentArcNeg_inter_spliceSquareBoundary] at hp
  refine Prod.ext ?_ (crossSeamResolveNeg_snd p)
  rw [crossSeamResolveNeg_fst]
  change crossSeamChordNeg p.1 = p.1
  rcases hp with h | h
  · rw [h]; exact crossSeamChordNeg_apply_negX
  · rw [Set.mem_singleton_iff.mp h]; exact crossSeamChordNeg_apply_posY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_eqOn_lateral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_eqOn_lateral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_eqOn_lateral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolveNeg_eqOn_lateral

theorem convex_spliceSquare : Convex ℝ spliceSquare :=
  (convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.convex_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.convex_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.convex_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.convex_spliceSquare

theorem segment_crossSeamResolvePos_subset {p : (ℝ × ℝ) × ℝ} (hp : p ∈ bentSheetPos) :
    segment ℝ p (crossSeamResolvePos p) ⊆ spliceSquare ×ˢ ({p.2} : Set ℝ) := by
  refine (convex_spliceSquare.prod (convex_singleton p.2)).segment_subset ?_ ?_
  · exact ⟨bentArcPos_subset_spliceSquare hp.1, rfl⟩
  · refine ⟨?_, crossSeamResolvePos_snd p⟩
    rw [crossSeamResolvePos_fst]
    exact Set.sep_subset _ _ (mapsTo_crossSeamChordPos hp.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolvePos_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolvePos_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolvePos_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolvePos_subset

theorem segment_crossSeamResolveNeg_subset {p : (ℝ × ℝ) × ℝ} (hp : p ∈ bentSheetNeg) :
    segment ℝ p (crossSeamResolveNeg p) ⊆ spliceSquare ×ˢ ({p.2} : Set ℝ) := by
  refine (convex_spliceSquare.prod (convex_singleton p.2)).segment_subset ?_ ?_
  · exact ⟨bentArcNeg_subset_spliceSquare hp.1, rfl⟩
  · refine ⟨?_, crossSeamResolveNeg_snd p⟩
    rw [crossSeamResolveNeg_fst]
    exact Set.sep_subset _ _ (mapsTo_crossSeamChordNeg hp.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolveNeg_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolveNeg_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolveNeg_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.segment_crossSeamResolveNeg_subset

theorem bentFigure_eq_union : bentFigure = bentSheetPos ∪ bentSheetNeg := by
  rw [bentFigure, bentSheetPos, bentSheetNeg, Set.union_prod]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_eq_union

theorem spliceFigure_eq_union : spliceFigure = spliceSheetPos ∪ spliceSheetNeg := by
  rw [spliceFigure, spliceSheetPos, spliceSheetNeg, Set.union_prod]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_eq_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_eq_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_eq_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_eq_union

def bentSource : Set (Bool × ((ℝ × ℝ) × ℝ)) :=
  {_root_.Bool.true} ×ˢ bentSheetPos ∪ {_root_.Bool.false} ×ˢ bentSheetNeg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentSource

theorem mem_bentSource {q : Bool × ((ℝ × ℝ) × ℝ)} :
    q ∈ bentSource ↔
      (q.1 = _root_.Bool.true ∧ q.2 ∈ bentSheetPos) ∨ (q.1 = _root_.Bool.false ∧ q.2 ∈ bentSheetNeg) := by
  simp only [bentSource, Set.mem_union, Set.mem_prod, Set.mem_singleton_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_bentSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_bentSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_bentSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_bentSource

def crossSeamInclude (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ := q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamInclude then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamInclude"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamInclude ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamInclude

noncomputable def crossSeamResolve (q : Bool × ((ℝ × ℝ) × ℝ)) : (ℝ × ℝ) × ℝ :=
  if q.1 then crossSeamResolvePos q.2 else crossSeamResolveNeg q.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve

theorem crossSeamResolve_true (x : (ℝ × ℝ) × ℝ) :
    crossSeamResolve (_root_.Bool.true, x) = crossSeamResolvePos x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_true then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_true"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_true ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_true

theorem crossSeamResolve_false (x : (ℝ × ℝ) × ℝ) :
    crossSeamResolve (_root_.Bool.false, x) = crossSeamResolveNeg x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_false then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_false"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_false ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_false

theorem injOn_crossSeamResolve : _root_.Set.InjOn crossSeamResolve bentSource := by
  rintro ⟨b, x⟩ hq ⟨b', x'⟩ hr hqr
  rcases mem_bentSource.mp hq with ⟨hb, hx⟩ | ⟨hb, hx⟩ <;>
    rcases mem_bentSource.mp hr with ⟨hb', hx'⟩ | ⟨hb', hx'⟩ <;>
      subst hb <;> subst hb'
  · rw [crossSeamResolve_true, crossSeamResolve_true] at hqr
    exact Prod.ext rfl (isPLHomeomorphOn_crossSeamResolvePos.bijOn.injOn hx hx' hqr)
  · exfalso
    rw [crossSeamResolve_true, crossSeamResolve_false] at hqr
    have h1 : crossSeamResolvePos x ∈ spliceSheetPos :=
      isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo hx
    rw [hqr] at h1
    exact Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg h1
      (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo hx')
  · exfalso
    rw [crossSeamResolve_false, crossSeamResolve_true] at hqr
    have h1 : crossSeamResolveNeg x ∈ spliceSheetNeg :=
      isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo hx
    rw [hqr] at h1
    exact Set.disjoint_left.mp disjoint_spliceSheetPos_spliceSheetNeg
      (isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo hx') h1
  · rw [crossSeamResolve_false, crossSeamResolve_false] at hqr
    exact Prod.ext rfl (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.injOn hx hx' hqr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamResolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamResolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamResolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.injOn_crossSeamResolve

theorem doublePointSet_crossSeamInclude :
    doublePointSet crossSeamInclude bentSource = spliceCore := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨b, x⟩, hq, ⟨b', x'⟩, hr, hne, hy1, hy2⟩
    have hx : x = y := hy1
    have hx' : x' = y := hy2
    have hbb : b ≠ b' := fun h => hne (Prod.ext h (hx.trans hx'.symm))
    rw [← bentSheetPos_inter_bentSheetNeg]
    rcases mem_bentSource.mp hq with ⟨hb, hs⟩ | ⟨hb, hs⟩ <;>
      rcases mem_bentSource.mp hr with ⟨hb', hs'⟩ | ⟨hb', hs'⟩
    · exact absurd (hb.trans hb'.symm) hbb
    · exact ⟨hx ▸ hs, hx' ▸ hs'⟩
    · exact ⟨hx' ▸ hs', hx ▸ hs⟩
    · exact absurd (hb.trans hb'.symm) hbb
  · intro y hy
    rw [← bentSheetPos_inter_bentSheetNeg] at hy
    exact ⟨(_root_.Bool.true, y), mem_bentSource.mpr (Or.inl ⟨rfl, hy.1⟩), (_root_.Bool.false, y),
      mem_bentSource.mpr (Or.inr ⟨rfl, hy.2⟩),
      fun h => Bool.noConfusion (congrArg Prod.fst h), rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamInclude then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamInclude"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamInclude ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamInclude

theorem doublePointSet_crossSeamResolve :
    doublePointSet crossSeamResolve bentSource = ∅ :=
  (doublePointSet_eq_empty_iff_injOn crossSeamResolve bentSource).mpr injOn_crossSeamResolve

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamResolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamResolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamResolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_crossSeamResolve

theorem image_crossSeamInclude : crossSeamInclude '' bentSource = bentFigure := by
  rw [bentFigure_eq_union]
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    rcases mem_bentSource.mp hq with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro x (hx | hx)
    · exact ⟨(_root_.Bool.true, x), mem_bentSource.mpr (Or.inl ⟨rfl, hx⟩), rfl⟩
    · exact ⟨(_root_.Bool.false, x), mem_bentSource.mpr (Or.inr ⟨rfl, hx⟩), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamInclude then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamInclude"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamInclude ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamInclude

theorem image_crossSeamResolve : crossSeamResolve '' bentSource = spliceFigure := by
  rw [spliceFigure_eq_union]
  apply Set.Subset.antisymm
  · rintro x ⟨⟨b, z⟩, hq, rfl⟩
    rcases mem_bentSource.mp hq with ⟨hb, h⟩ | ⟨hb, h⟩ <;> subst hb
    · exact Or.inl (isPLHomeomorphOn_crossSeamResolvePos.bijOn.mapsTo h)
    · exact Or.inr (isPLHomeomorphOn_crossSeamResolveNeg.bijOn.mapsTo h)
  · rintro x (hx | hx)
    · obtain ⟨z, hz, rfl⟩ := isPLHomeomorphOn_crossSeamResolvePos.bijOn.surjOn hx
      exact ⟨(_root_.Bool.true, z), mem_bentSource.mpr (Or.inl ⟨rfl, hz⟩), rfl⟩
    · obtain ⟨z, hz, rfl⟩ := isPLHomeomorphOn_crossSeamResolveNeg.bijOn.surjOn hx
      exact ⟨(_root_.Bool.false, z), mem_bentSource.mpr (Or.inr ⟨rfl, hz⟩), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamResolve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamResolve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamResolve ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_crossSeamResolve

namespace NormalSingularSetTriangulation

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D D' : SingularTwoCell M} {BdM BdM' : Set M}

theorem complexity_lt_of_branchEquiv_compl (T : NormalSingularSetTriangulation D BdM)
    (T' : NormalSingularSetTriangulation D' BdM') {c : T.Branch}
    (e : T'.Branch ≃ {b : T.Branch // b ≠ c}) :
    T'.complexity < T.complexity :=
  T.complexity_lt_of_injective_origin T' c (fun b => (e b).1)
    (fun _ _ h => e.injective (Subtype.ext h)) fun b => (e b).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.complexity_lt_of_branchEquiv_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.complexity_lt_of_branchEquiv_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.complexity_lt_of_branchEquiv_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularSetTriangulation.complexity_lt_of_branchEquiv_compl

end NormalSingularSetTriangulation

structure CrossSeamResolutionData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (U : Set M) where
  cell : SingularTwoCell M
  normal : NormalSingularCellData cell BdM B
  doublePointSet_eq : doublePointSet cell cell.domain =
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c
  branchEquiv : normal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c}
  branchCarrier_eq : ∀ b, normal.singularSet.branchCarrier b =
    hD.singularSet.branchCarrier (branchEquiv b).1
  image_subset : cell '' cell.domain ⊆ D '' D.domain ∪ U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData

namespace CrossSeamResolutionData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

theorem complexity_lt (R : CrossSeamResolutionData hD c U) :
    R.normal.singularSet.complexity < hD.singularSet.complexity :=
  hD.singularSet.complexity_lt_of_branchEquiv_compl R.normal.singularSet R.branchEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.complexity_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.complexity_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.complexity_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.complexity_lt

theorem doublePointSet_subset (R : CrossSeamResolutionData hD c U) :
    doublePointSet R.cell R.cell.domain ⊆ doublePointSet D D.domain := by
  rw [R.doublePointSet_eq]
  exact Set.sdiff_subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.doublePointSet_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.doublePointSet_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.doublePointSet_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.doublePointSet_subset

theorem disjoint_branchCarrier (R : CrossSeamResolutionData hD c U) :
    Disjoint (doublePointSet R.cell R.cell.domain) (hD.singularSet.branchCarrier c) := by
  rw [R.doublePointSet_eq]
  exact Set.disjoint_sdiff_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.disjoint_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.disjoint_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.disjoint_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.disjoint_branchCarrier

theorem branchCarrier_mem_range (R : CrossSeamResolutionData hD c U)
    (b : R.normal.singularSet.Branch) :
    R.normal.singularSet.branchCarrier b ∈
      Set.range (hD.singularSet.branchCarrier ∘ fun b' : {b' // b' ≠ c} => b'.1) :=
  ⟨R.branchEquiv b, (R.branchCarrier_eq b).symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.branchCarrier_mem_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.branchCarrier_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.branchCarrier_mem_range ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamResolutionData.branchCarrier_mem_range

end CrossSeamResolutionData

end DifferentialGeometry.Topology.PiecewiseLinear
