/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem doublePointSet_congr {X Y : Type*} {f g : X → Y} {P : Set X} (h : _root_.Set.EqOn f g P) :
    doublePointSet f P = doublePointSet g P := by
  ext y
  constructor
  · rintro ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨x, hx, z, hz, hxz, (h hx).symm.trans hfx, (h hz).symm.trans hfz⟩
  · rintro ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨x, hx, z, hz, hxz, (h hx).trans hfx, (h hz).trans hfz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_congr ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_congr

theorem doublePointSet_comp_of_bijOn {X Y Z : Type*} {e : X → Y} {f : Y → Z} {P : Set X}
    {Q : Set Y} (he : _root_.Set.BijOn e P Q) : doublePointSet (f ∘ e) P = doublePointSet f Q := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    exact ⟨e x, he.mapsTo hx, e z, he.mapsTo hz, fun h => hxz (he.injOn hx hz h), hfx, hfz⟩
  · rintro y ⟨a, ha, b, hb, hab, hfa, hfb⟩
    obtain ⟨x, hx, rfl⟩ := he.surjOn ha
    obtain ⟨z, hz, rfl⟩ := he.surjOn hb
    exact ⟨x, hx, z, hz, fun h => hab (congrArg e h), hfa, hfb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_comp_of_bijOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_comp_of_bijOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_comp_of_bijOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.doublePointSet_comp_of_bijOn

theorem image_doublePointSet_of_injOn {X Y Z : Type*} {f : X → Y} {g : Y → Z} {P : Set X}
    (hg : _root_.Set.InjOn g (f '' P)) : doublePointSet (g ∘ f) P = g '' doublePointSet f P := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hfx, hfz⟩
    have h : f x = f z := hg ⟨x, hx, rfl⟩ ⟨z, hz, rfl⟩ (hfx.trans hfz.symm)
    exact ⟨f x, ⟨x, hx, z, hz, hxz, rfl, h.symm⟩, hfx⟩
  · rintro _ ⟨w, ⟨x, hx, z, hz, hxz, hfx, hfz⟩, rfl⟩
    exact ⟨x, hx, z, hz, hxz, congrArg g hfx, congrArg g hfz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_doublePointSet_of_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_doublePointSet_of_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_doublePointSet_of_injOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_doublePointSet_of_injOn

theorem spliceCore_subset_spliceCylinder : spliceCore ⊆ spliceCylinder := by
  intro p hp
  refine ⟨?_, hp.2⟩
  have h : p.1 = ((0 : ℝ), (0 : ℝ)) := hp.1
  rw [h, mem_spliceSquare]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_spliceCylinder

theorem crossingFigure_subset_spliceCylinder : crossingFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨h.1, ht⟩
  · exact ⟨h.1, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_spliceCylinder

theorem spliceFigure_subset_spliceCylinder : spliceFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨h.1, ht⟩
  · exact ⟨h.1, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_subset_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_subset_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_subset_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceFigure_subset_spliceCylinder

theorem bentFigure_subset_spliceCylinder : bentFigure ⊆ spliceCylinder := by
  rintro p ⟨h | h, ht⟩
  · exact ⟨bentArcPos_subset_spliceSquare h, ht⟩
  · exact ⟨bentArcNeg_subset_spliceSquare h, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_subset_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_subset_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_subset_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.bentFigure_subset_spliceCylinder

theorem spliceSquareBoundary_prod_subset_spliceCylinder :
    spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆ spliceCylinder := by
  rintro p ⟨h, ht⟩
  exact ⟨h.1, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareBoundary_prod_subset_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareBoundary_prod_subset_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareBoundary_prod_subset_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceSquareBoundary_prod_subset_spliceCylinder

def spliceEndDisks : Set ((ℝ × ℝ) × ℝ) := spliceSquare ×ˢ ({0, 1} : Set ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks

theorem spliceEndDisks_subset_spliceCylinder : spliceEndDisks ⊆ spliceCylinder := by
  rintro p ⟨hp, ht⟩
  refine ⟨hp, ?_⟩
  rcases ht with h | h
  · rw [h]
    exact ⟨le_refl (0 : ℝ), zero_le_one⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨zero_le_one, le_refl (1 : ℝ)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks_subset_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks_subset_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks_subset_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEndDisks_subset_spliceCylinder

theorem crossSeamResolve_snd (q : Bool × ((ℝ × ℝ) × ℝ)) : (crossSeamResolve q).2 = q.2.2 := by
  obtain ⟨b, x⟩ := q
  cases b
  · exact crossSeamResolveNeg_snd x
  · exact crossSeamResolvePos_snd x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_snd ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_snd

theorem crossSeamResolve_mem_spliceEndDisks {q : Bool × ((ℝ × ℝ) × ℝ)} (hq : q ∈ bentSource)
    (hend : q.2.2 = 0 ∨ q.2.2 = 1) : crossSeamResolve q ∈ spliceEndDisks := by
  have hfig : crossSeamResolve q ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨q, hq, rfl⟩
  refine ⟨(spliceFigure_subset_spliceCylinder hfig).1, ?_⟩
  rw [crossSeamResolve_snd]
  rcases hend with h | h
  · exact Or.inl h
  · exact Or.inr (Set.mem_singleton_iff.mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_mem_spliceEndDisks then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_mem_spliceEndDisks"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_mem_spliceEndDisks ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolve_mem_spliceEndDisks

structure CrossSeamTubeCore {M : Type u} [TopologicalSpace M] (chart : (ℝ × ℝ) × ℝ → M)
    (figure double branch tube : Set M) : Prop where
  isOpen_tube : IsOpen tube
  continuousOn_chart : ContinuousOn chart spliceCylinder
  injOn_chart : _root_.Set.InjOn chart spliceCylinder
  image_subset_tube : chart '' spliceCylinder ⊆ tube
  image_spliceCore : chart '' spliceCore = branch
  image_crossingFigure : chart '' crossingFigure = figure ∩ chart '' spliceCylinder
  double_inter_tube : double ∩ tube = branch

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeCore

noncomputable def spliceEmbedding : ((ℝ × ℝ) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding

def tubeWitnessSheetX : Set ((ℝ × ℝ) × ℝ) := crossingArcX ×ˢ _root_.Set.Icc (0 : ℝ) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX

def tubeWitnessFarArcX : Set (ℝ × ℝ) := ({(4 : ℝ)} : Set ℝ) ×ˢ _root_.Set.Icc (3 : ℝ) 5

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX

def tubeWitnessFarArcY : Set (ℝ × ℝ) := _root_.Set.Icc (3 : ℝ) 5 ×ˢ ({(4 : ℝ)} : Set ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcY

def tubeWitnessFarSheetX : Set ((ℝ × ℝ) × ℝ) := tubeWitnessFarArcX ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX

def tubeWitnessFarSheetY : Set ((ℝ × ℝ) × ℝ) := tubeWitnessFarArcY ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetY

def tubeWitnessFarCore : Set ((ℝ × ℝ) × ℝ) :=
  ({((4 : ℝ), (4 : ℝ))} : Set (ℝ × ℝ)) ×ˢ _root_.Set.Icc (0 : ℝ) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarCore

def tubeWitnessSurface : Set ((ℝ × ℝ) × ℝ) :=
  tubeWitnessSheetX ∪ crossingSheetY ∪ tubeWitnessFarSheetX ∪ tubeWitnessFarSheetY

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface

def tubeWitnessDouble : Set ((ℝ × ℝ) × ℝ) := spliceCore ∪ tubeWitnessFarCore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble

def tubeWitnessTube : Set ((ℝ × ℝ) × ℝ) :=
  (_root_.Set.Ioo (-2 : ℝ) 2 ×ˢ _root_.Set.Ioo (-2 : ℝ) 2) ×ˢ _root_.Set.Ioo (-1 : ℝ) 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTube

theorem tubeWitnessFarArcX_inter_tubeWitnessFarArcY :
    tubeWitnessFarArcX ∩ tubeWitnessFarArcY = {((4 : ℝ), (4 : ℝ))} := by
  ext p
  simp only [tubeWitnessFarArcX, tubeWitnessFarArcY, Set.mem_inter_iff, Set.mem_prod,
    Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, -, h2⟩
    exact Prod.ext h1 h2
  · rintro rfl
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX_inter_tubeWitnessFarArcY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX_inter_tubeWitnessFarArcY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX_inter_tubeWitnessFarArcY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarArcX_inter_tubeWitnessFarArcY

theorem tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY :
    tubeWitnessFarSheetX ∩ tubeWitnessFarSheetY = tubeWitnessFarCore := by
  rw [tubeWitnessFarSheetX, tubeWitnessFarSheetY, Set.prod_inter_prod, Set.inter_self,
    tubeWitnessFarArcX_inter_tubeWitnessFarArcY, tubeWitnessFarCore]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFarSheetX_inter_tubeWitnessFarSheetY

theorem tubeWitnessSheetX_inter_crossingSheetY :
    tubeWitnessSheetX ∩ crossingSheetY = spliceCore := by
  have h : _root_.Set.Icc (0 : ℝ) 2 ∩ _root_.Set.Icc (0 : ℝ) 1 = _root_.Set.Icc (0 : ℝ) 1 :=
    Set.inter_eq_right.mpr (Set.Icc_subset_Icc le_rfl (by norm_num))
  rw [tubeWitnessSheetX, crossingSheetY, Set.prod_inter_prod, crossingArcX_inter_crossingArcY,
    h, spliceCore]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX_inter_crossingSheetY then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX_inter_crossingSheetY"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX_inter_crossingSheetY ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSheetX_inter_crossingSheetY

theorem disjoint_tubeWitnessFarArc_spliceSquare :
    Disjoint (tubeWitnessFarArcX ∪ tubeWitnessFarArcY) spliceSquare := by
  rw [Set.disjoint_left]
  rintro q (h | h) hq
  · rw [mem_spliceSquare] at hq
    have h4 : q.1 = 4 := h.1
    linarith [hq.1.2]
  · rw [mem_spliceSquare] at hq
    have h4 : q.2 = 4 := h.2
    linarith [hq.2.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessFarArc_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessFarArc_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessFarArc_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessFarArc_spliceSquare

theorem disjoint_tubeWitnessNear_tubeWitnessFar :
    Disjoint (tubeWitnessSheetX ∪ crossingSheetY)
      (tubeWitnessFarSheetX ∪ tubeWitnessFarSheetY) := by
  rw [Set.disjoint_left]
  intro p hnear hfar
  have hsq : p.1 ∈ spliceSquare := by
    rcases hnear with h | h
    · exact h.1.1
    · exact h.1.1
  have hfarArc : p.1 ∈ tubeWitnessFarArcX ∪ tubeWitnessFarArcY := by
    rcases hfar with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  exact Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare hfarArc hsq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessNear_tubeWitnessFar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessNear_tubeWitnessFar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessNear_tubeWitnessFar ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_tubeWitnessNear_tubeWitnessFar

theorem tubeWitnessSurface_inter_spliceCylinder :
    tubeWitnessSurface ∩ spliceCylinder = crossingFigure := by
  ext p
  constructor
  · rintro ⟨((h | h) | h) | h, hcyl⟩
    · exact ⟨Or.inl h.1, hcyl.2⟩
    · exact ⟨Or.inr h.1, h.2⟩
    · exact absurd hcyl.1
        (Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare (Or.inl h.1))
    · exact absurd hcyl.1
        (Set.disjoint_left.mp disjoint_tubeWitnessFarArc_spliceSquare (Or.inr h.1))
  · rintro ⟨h | h, ht⟩
    · exact ⟨Or.inl (Or.inl (Or.inl ⟨h, Set.Icc_subset_Icc le_rfl (by norm_num) ht⟩)), h.1, ht⟩
    · exact ⟨Or.inl (Or.inl (Or.inr ⟨h, ht⟩)), h.1, ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface_inter_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface_inter_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface_inter_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessSurface_inter_spliceCylinder

theorem crossingFigure_subset_tubeWitnessSurface : crossingFigure ⊆ tubeWitnessSurface := by
  rintro p ⟨h | h, ht⟩
  · exact Or.inl (Or.inl (Or.inl ⟨h, Set.Icc_subset_Icc le_rfl (by norm_num) ht⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨h, ht⟩))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_tubeWitnessSurface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_tubeWitnessSurface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_tubeWitnessSurface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossingFigure_subset_tubeWitnessSurface

theorem spliceCore_subset_tubeWitnessDouble : spliceCore ⊆ tubeWitnessDouble :=
  Set.subset_union_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_tubeWitnessDouble then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_tubeWitnessDouble"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_tubeWitnessDouble ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceCore_subset_tubeWitnessDouble

theorem spliceCylinder_subset_tubeWitnessTube : spliceCylinder ⊆ tubeWitnessTube := by
  rintro p ⟨hsq, ht⟩
  rw [mem_spliceSquare] at hsq
  rw [Set.mem_Icc] at ht
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> constructor <;>
    linarith [hsq.1.1, hsq.1.2, hsq.2.1, hsq.2.2, ht.1, ht.2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceCylinder_subset_tubeWitnessTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceCylinder_subset_tubeWitnessTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceCylinder_subset_tubeWitnessTube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceCylinder_subset_tubeWitnessTube

theorem isOpen_tubeWitnessTube : IsOpen tubeWitnessTube :=
  (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_tubeWitnessTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOpen_tubeWitnessTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_tubeWitnessTube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOpen_tubeWitnessTube

theorem tubeWitnessDouble_inter_tubeWitnessTube :
    tubeWitnessDouble ∩ tubeWitnessTube = spliceCore := by
  apply Subset.antisymm
  · rintro p ⟨hd | hd, hu⟩
    · exact hd
    · exfalso
      have h4 : p.1 = ((4 : ℝ), (4 : ℝ)) := hd.1
      have hlt : p.1.1 < 2 := hu.1.1.2
      rw [h4] at hlt
      norm_num at hlt
  · intro p hp
    exact ⟨Or.inl hp,
      spliceCylinder_subset_tubeWitnessTube (spliceCore_subset_spliceCylinder hp)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble_inter_tubeWitnessTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble_inter_tubeWitnessTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble_inter_tubeWitnessTube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessDouble_inter_tubeWitnessTube

theorem tubeWitnessTop_mem_surface :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∈ tubeWitnessSurface := by
  refine Or.inl (Or.inl (Or.inl ⟨⟨?_, rfl⟩, ?_⟩))
  · rw [mem_spliceSquare]
    norm_num
  · rw [Set.mem_Icc]
    norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_mem_surface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_mem_surface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_mem_surface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_mem_surface

theorem tubeWitnessTop_notMem_crossingFigure :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∉ crossingFigure := by
  rintro ⟨-, ht⟩
  rw [Set.mem_Icc] at ht
  norm_num at ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_crossingFigure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_crossingFigure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_crossingFigure ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_crossingFigure

theorem tubeWitnessTop_notMem_tube :
    (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) ∉ tubeWitnessTube := by
  intro h
  have h2 : (((0 : ℝ), (0 : ℝ)), (2 : ℝ)).2 < 2 := h.2.2
  norm_num at h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessTop_notMem_tube

theorem tubeWitnessFar_mem_double :
    (((4 : ℝ), (4 : ℝ)), (0 : ℝ)) ∈ tubeWitnessDouble := by
  refine Or.inr ⟨rfl, ?_⟩
  rw [Set.mem_Icc]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_mem_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_mem_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_mem_double ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_mem_double

theorem tubeWitnessFar_notMem_spliceCore :
    (((4 : ℝ), (4 : ℝ)), (0 : ℝ)) ∉ spliceCore := by
  rintro ⟨h, -⟩
  have h4 : ((4 : ℝ), (4 : ℝ)) = ((0 : ℝ), (0 : ℝ)) := h
  rw [Prod.mk.injEq] at h4
  norm_num at h4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_notMem_spliceCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_notMem_spliceCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_notMem_spliceCore ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.tubeWitnessFar_notMem_spliceCore

theorem spliceEmbedding_image_ssubset {s t : Set ((ℝ × ℝ) × ℝ)} (hst : s ⊆ t)
    {p : (ℝ × ℝ) × ℝ} (hpt : p ∈ t) (hps : p ∉ s) :
    ⇑spliceEmbedding '' s ⊂ ⇑spliceEmbedding '' t := by
  rw [Set.ssubset_iff_of_subset (Set.image_mono hst)]
  refine ⟨spliceEmbedding p, ⟨p, hpt, rfl⟩, ?_⟩
  rintro ⟨q, hq, hqe⟩
  have hqp : q = p := spliceEmbedding.injective hqe
  rw [hqp] at hq
  exact hps hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_ssubset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_ssubset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_ssubset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_ssubset

theorem spliceEmbedding_image_spliceCore_eq_inter :
    ⇑spliceEmbedding '' spliceCore =
      ⇑spliceEmbedding '' tubeWitnessSheetX ∩ ⇑spliceEmbedding '' crossingSheetY := by
  rw [← tubeWitnessSheetX_inter_crossingSheetY,
    Set.InjOn.image_inter spliceEmbedding.injective.injOn (_root_.Set.subset_univ _) (_root_.Set.subset_univ _)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_eq_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_eq_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_eq_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_eq_inter

theorem crossSeamTubeCore_spliceEmbedding :
    CrossSeamTubeCore (M := EuclideanSpace ℝ (Fin 3)) ⇑spliceEmbedding
      (⇑spliceEmbedding '' tubeWitnessSurface) (⇑spliceEmbedding '' tubeWitnessDouble)
      (⇑spliceEmbedding '' spliceCore) (⇑spliceEmbedding '' tubeWitnessTube) where
  isOpen_tube := by
    have h : IsOpen (⇑spliceEmbedding.toHomeomorph '' tubeWitnessTube) :=
      spliceEmbedding.toHomeomorph.isOpenMap _ isOpen_tubeWitnessTube
    exact h
  continuousOn_chart := spliceEmbedding.continuous.continuousOn
  injOn_chart := spliceEmbedding.injective.injOn
  image_subset_tube := Set.image_mono spliceCylinder_subset_tubeWitnessTube
  image_spliceCore := rfl
  image_crossingFigure := by
    rw [← Set.InjOn.image_inter spliceEmbedding.injective.injOn (_root_.Set.subset_univ _)
      (_root_.Set.subset_univ _), tubeWitnessSurface_inter_spliceCylinder]
  double_inter_tube := by
    rw [← Set.InjOn.image_inter spliceEmbedding.injective.injOn (_root_.Set.subset_univ _)
      (_root_.Set.subset_univ _), tubeWitnessDouble_inter_tubeWitnessTube]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamTubeCore_spliceEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamTubeCore_spliceEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamTubeCore_spliceEmbedding ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamTubeCore_spliceEmbedding

theorem spliceEmbedding_image_crossingFigure_ssubset_surface :
    ⇑spliceEmbedding '' crossingFigure ⊂ ⇑spliceEmbedding '' tubeWitnessSurface :=
  spliceEmbedding_image_ssubset crossingFigure_subset_tubeWitnessSurface
    tubeWitnessTop_mem_surface tubeWitnessTop_notMem_crossingFigure

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_crossingFigure_ssubset_surface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_crossingFigure_ssubset_surface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_crossingFigure_ssubset_surface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_crossingFigure_ssubset_surface

theorem spliceEmbedding_surface_not_subset_tube :
    ¬⇑spliceEmbedding '' tubeWitnessSurface ⊆ ⇑spliceEmbedding '' tubeWitnessTube := by
  intro h
  obtain ⟨q, hq, hqe⟩ := h ⟨_, tubeWitnessTop_mem_surface, rfl⟩
  have hqp : q = (((0 : ℝ), (0 : ℝ)), (2 : ℝ)) := spliceEmbedding.injective hqe
  rw [hqp] at hq
  exact tubeWitnessTop_notMem_tube hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_surface_not_subset_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_surface_not_subset_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_surface_not_subset_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_surface_not_subset_tube

theorem spliceEmbedding_image_spliceCore_ssubset_double :
    ⇑spliceEmbedding '' spliceCore ⊂ ⇑spliceEmbedding '' tubeWitnessDouble :=
  spliceEmbedding_image_ssubset spliceCore_subset_tubeWitnessDouble
    tubeWitnessFar_mem_double tubeWitnessFar_notMem_spliceCore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_ssubset_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_ssubset_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_ssubset_double ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.spliceEmbedding_image_spliceCore_ssubset_double

structure CrossSeamTubeData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B : Set M}
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) (U : Set M) where
  chart : (ℝ × ℝ) × ℝ → M
  isTube : CrossSeamTubeCore chart (D '' D.domain) (doublePointSet D D.domain)
    (hD.singularSet.branchCarrier c) U

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData

namespace CrossSeamTubeData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch}

theorem branchCarrier_subset_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ T.chart '' spliceCylinder := by
  rw [← T.isTube.image_spliceCore]
  exact Set.image_mono spliceCore_subset_spliceCylinder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_image_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_image_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_image_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_image_spliceCylinder

theorem branchCarrier_subset_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ U :=
  T.branchCarrier_subset_image_spliceCylinder.trans T.isTube.image_subset_tube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_tube

theorem branchCarrier_subset_interior_tube (T : CrossSeamTubeData hD c U) :
    hD.singularSet.branchCarrier c ⊆ interior U := by
  rw [T.isTube.isOpen_tube.interior_eq]
  exact T.branchCarrier_subset_tube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_interior_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_interior_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_interior_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.branchCarrier_subset_interior_tube

theorem isCompact_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    IsCompact (T.chart '' spliceCylinder) :=
  isHPolytope_spliceCylinder.isPolyhedron.isCompact.image_of_continuousOn
    T.isTube.continuousOn_chart

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.isCompact_image_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.isCompact_image_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.isCompact_image_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.isCompact_image_spliceCylinder

theorem doublePointSet_sdiff_branchCarrier (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c =
      doublePointSet D D.domain \ U := by
  apply Subset.antisymm
  · rintro y ⟨hy, hyb⟩
    refine ⟨hy, fun hyU => hyb ?_⟩
    rw [← T.isTube.double_inter_tube]
    exact ⟨hy, hyU⟩
  · rintro y ⟨hy, hyU⟩
    exact ⟨hy, fun hyb => hyU (T.branchCarrier_subset_tube hyb)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_branchCarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_branchCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_branchCarrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_branchCarrier

theorem doublePointSet_inter_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain ∩ T.chart '' spliceCylinder =
      hD.singularSet.branchCarrier c := by
  apply Subset.antisymm
  · rintro y ⟨hy, hcyl⟩
    rw [← T.isTube.double_inter_tube]
    exact ⟨hy, T.isTube.image_subset_tube hcyl⟩
  · intro y hy
    refine ⟨?_, T.branchCarrier_subset_image_spliceCylinder hy⟩
    rw [← T.isTube.double_inter_tube] at hy
    exact hy.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_inter_image_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_inter_image_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_inter_image_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_inter_image_spliceCylinder

theorem doublePointSet_sdiff_image_spliceCylinder (T : CrossSeamTubeData hD c U) :
    doublePointSet D D.domain \ hD.singularSet.branchCarrier c =
      doublePointSet D D.domain \ T.chart '' spliceCylinder := by
  apply Subset.antisymm
  · rintro y ⟨hy, hyb⟩
    refine ⟨hy, fun hcyl => hyb ?_⟩
    rw [← T.doublePointSet_inter_image_spliceCylinder]
    exact ⟨hy, hcyl⟩
  · rintro y ⟨hy, hcyl⟩
    exact ⟨hy, fun hyb => hcyl (T.branchCarrier_subset_image_spliceCylinder hyb)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamTubeData.doublePointSet_sdiff_image_spliceCylinder

end CrossSeamTubeData

structure CrossSeamRegluedData {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {D : SingularTwoCell M} {BdM B U : Set M}
    {hD : NormalSingularCellData D BdM B} {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) (G : SingularTwoCell M) where
  cell : SingularTwoCell M
  domain_eq : cell.domain = G.domain
  coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)
  bijOn_coord : _root_.Set.BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource
  reglued_eq : _root_.Set.EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
    (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  resolved_eq : _root_.Set.EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
    (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
  eqOn_compl : _root_.Set.EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData

namespace CrossSeamRegluedData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

theorem image_cell_tube (R : CrossSeamRegluedData T G) :
    R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = T.chart '' spliceFigure := by
  have h : R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = (T.chart ∘ crossSeamResolve ∘ R.coord) ''
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    Set.image_congr fun x hx => R.resolved_eq hx
  rw [h, Set.image_comp, Set.image_comp, R.bijOn_coord.image_eq, image_crossSeamResolve]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_tube

theorem mapsTo_cell_tube (R : CrossSeamRegluedData T G) :
    _root_.Set.MapsTo R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      (T.chart '' spliceCylinder) := by
  intro x hx
  have h : R.cell x ∈ R.cell '' (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := ⟨x, hx, rfl⟩
  rw [R.image_cell_tube] at h
  exact Set.image_mono spliceFigure_subset_spliceCylinder h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mapsTo_cell_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mapsTo_cell_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mapsTo_cell_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mapsTo_cell_tube

theorem injOn_cell_tube (R : CrossSeamRegluedData T G) :
    InjOn R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) := by
  intro x hx z hz hxz
  have hxm : R.coord x ∈ bentSource := R.bijOn_coord.mapsTo hx
  have hzm : R.coord z ∈ bentSource := R.bijOn_coord.mapsTo hz
  have hxs : crossSeamResolve (R.coord x) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hxm, rfl⟩
  have hzs : crossSeamResolve (R.coord z) ∈ spliceFigure := by
    rw [← image_crossSeamResolve]
    exact ⟨_, hzm, rfl⟩
  rw [R.resolved_eq hx, R.resolved_eq hz] at hxz
  simp only [Function.comp_apply] at hxz
  have hmodel : crossSeamResolve (R.coord x) = crossSeamResolve (R.coord z) :=
    T.isTube.injOn_chart (spliceFigure_subset_spliceCylinder hxs)
      (spliceFigure_subset_spliceCylinder hzs) hxz
  exact R.bijOn_coord.injOn hx hz (injOn_crossSeamResolve hxm hzm hmodel)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.injOn_cell_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.injOn_cell_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.injOn_cell_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.injOn_cell_tube

theorem doublePointSet_cell_tube (R : CrossSeamRegluedData T G) :
    doublePointSet R.cell (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) = ∅ :=
  (doublePointSet_eq_empty_iff_injOn _ _).mpr R.injOn_cell_tube

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_tube

theorem doublePointSet_reglued_tube (R : CrossSeamRegluedData T G) :
    doublePointSet G (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) =
      hD.singularSet.branchCarrier c := by
  have hinj : _root_.Set.InjOn T.chart (crossSeamInclude '' bentSource) := by
    rw [image_crossSeamInclude]
    exact T.isTube.injOn_chart.mono bentFigure_subset_spliceCylinder
  have hcongr : doublePointSet G (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder))
      = doublePointSet ((T.chart ∘ crossSeamInclude) ∘ R.coord)
        (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :=
    doublePointSet_congr R.reglued_eq
  rw [hcongr, doublePointSet_comp_of_bijOn R.bijOn_coord,
    image_doublePointSet_of_injOn hinj, doublePointSet_crossSeamInclude,
    T.isTube.image_spliceCore]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_reglued_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_reglued_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_reglued_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_reglued_tube

theorem cell_notMem_tube (R : CrossSeamRegluedData T G) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)) :
    R.cell x ∉ T.chart '' spliceCylinder := by
  rw [R.eqOn_compl hx]
  exact hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.cell_notMem_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.cell_notMem_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.cell_notMem_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.cell_notMem_tube

theorem mem_tube_or_notMem_tube (G : SingularTwoCell M) (U : Set M)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ G.domain) :
    x ∈ G.domain ∩ ⇑G ⁻¹' U ∨ x ∈ G.domain \ ⇑G ⁻¹' U := by
  by_cases h : G x ∈ U
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mem_tube_or_notMem_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mem_tube_or_notMem_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mem_tube_or_notMem_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.mem_tube_or_notMem_tube

theorem doublePointSet_cell_eq (R : CrossSeamRegluedData T G)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder) :
    doublePointSet R.cell R.cell.domain =
      doublePointSet D D.domain \ hD.singularSet.branchCarrier c := by
  rw [T.doublePointSet_sdiff_image_spliceCylinder, ← hGD, R.domain_eq]
  apply Subset.antisymm
  · rintro y ⟨x, hx, z, hz, hxz, hyx, hyz⟩
    rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW <;>
      rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hz with hzV | hzW
    · exact absurd (R.injOn_cell_tube hxV hzV (hyx.trans hyz.symm)) hxz
    · exfalso
      have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyx]; exact R.mapsTo_cell_tube hxV
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyz]; exact R.cell_notMem_tube hzW
      exact h2 h1
    · exfalso
      have h1 : y ∈ T.chart '' spliceCylinder := by
        rw [← hyz]; exact R.mapsTo_cell_tube hzV
      have h2 : y ∉ T.chart '' spliceCylinder := by
        rw [← hyx]; exact R.cell_notMem_tube hxW
      exact h2 h1
    · refine ⟨⟨x, hx, z, hz, hxz, ?_, ?_⟩, ?_⟩
      · rw [← R.eqOn_compl hxW]; exact hyx
      · rw [← R.eqOn_compl hzW]; exact hyz
      · rw [← hyx]; exact R.cell_notMem_tube hxW
  · rintro y ⟨⟨x, hx, z, hz, hxz, hyx, hyz⟩, hyU⟩
    have hxU : G x ∉ T.chart '' spliceCylinder := by rw [hyx]; exact hyU
    have hzU : G z ∉ T.chart '' spliceCylinder := by rw [hyz]; exact hyU
    exact ⟨x, hx, z, hz, hxz, (R.eqOn_compl ⟨hx, hxU⟩).trans hyx,
      (R.eqOn_compl ⟨hz, hzU⟩).trans hyz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.doublePointSet_cell_eq

theorem image_cell_subset (R : CrossSeamRegluedData T G)
    (hGim : G '' G.domain ⊆ D '' D.domain) :
    R.cell '' R.cell.domain ⊆ D '' D.domain ∪ U := by
  rw [R.domain_eq]
  rintro _ ⟨x, hx, rfl⟩
  rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW
  · exact Or.inr (T.isTube.image_subset_tube (R.mapsTo_cell_tube hxV))
  · exact Or.inl (hGim ⟨x, hx, (R.eqOn_compl hxW).symm⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_subset

theorem image_cell_inter_lateral (R : CrossSeamRegluedData T G) :
    R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) =
      D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
  have hlat : T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ T.chart '' spliceCylinder :=
    Set.image_mono spliceSquareBoundary_prod_subset_spliceCylinder
  have hleft : R.cell '' R.cell.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      = T.chart '' spliceFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, hy⟩
      rw [R.domain_eq] at hx
      rcases mem_tube_or_notMem_tube G (T.chart '' spliceCylinder) hx with hxV | hxW
      · refine ⟨?_, hy⟩
        rw [← R.image_cell_tube]
        exact ⟨x, hxV, rfl⟩
      · exact absurd (hlat hy) (R.cell_notMem_tube hxW)
    · rintro y ⟨hy1, hy2⟩
      rw [← R.image_cell_tube] at hy1
      obtain ⟨x, hx, rfl⟩ := hy1
      exact ⟨⟨x, by rw [R.domain_eq]; exact hx.1, rfl⟩, hy2⟩
  have hright : D '' D.domain ∩ T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1)
      = T.chart '' crossingFigure ∩ T.chart '' (spliceSquareBoundary ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rw [T.isTube.image_crossingFigure, Set.inter_assoc, Set.inter_eq_right.mpr hlat]
  rw [hleft, hright,
    ← Set.InjOn.image_inter T.isTube.injOn_chart spliceFigure_subset_spliceCylinder
      spliceSquareBoundary_prod_subset_spliceCylinder,
    ← Set.InjOn.image_inter T.isTube.injOn_chart crossingFigure_subset_spliceCylinder
      spliceSquareBoundary_prod_subset_spliceCylinder,
    crossingFigure_inter_lateral_eq_spliceFigure_inter_lateral]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_inter_lateral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_inter_lateral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_inter_lateral ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CrossSeamRegluedData.image_cell_inter_lateral

end CrossSeamRegluedData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D G : SingularTwoCell M} {BdM B U : Set M} {hD : NormalSingularCellData D BdM B}
  {c : hD.singularSet.Branch} {T : CrossSeamTubeData hD c U}

theorem exists_resolved_cell_of_tube (R : CrossSeamRegluedData T G)
    (hnormal : NormalSingularCellData R.cell BdM B)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder) :
    ∃ (cell : SingularTwoCell M) (_hcell : NormalSingularCellData cell BdM B),
      doublePointSet cell cell.domain =
          doublePointSet D D.domain \ hD.singularSet.branchCarrier c ∧
        cell '' cell.domain ⊆ D '' D.domain ∪ U :=
  ⟨R.cell, hnormal, R.doublePointSet_cell_eq hGD, R.image_cell_subset hGim⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_resolved_cell_of_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_resolved_cell_of_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_resolved_cell_of_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_resolved_cell_of_tube

def crossSeamResolutionDataOfTube (R : CrossSeamRegluedData T G)
    (hnormal : NormalSingularCellData R.cell BdM B)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
    (e : hnormal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (he : ∀ b, hnormal.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (e b).1) :
    CrossSeamResolutionData hD c U where
  cell := R.cell
  normal := hnormal
  doublePointSet_eq := R.doublePointSet_cell_eq hGD
  branchEquiv := e
  branchCarrier_eq := he
  image_subset := R.image_cell_subset hGim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolutionDataOfTube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolutionDataOfTube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolutionDataOfTube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.crossSeamResolutionDataOfTube

theorem complexity_lt_of_tube (R : CrossSeamRegluedData T G)
    (hnormal : NormalSingularCellData R.cell BdM B)
    (hGim : G '' G.domain ⊆ D '' D.domain)
    (hGD : doublePointSet G G.domain \ T.chart '' spliceCylinder =
      doublePointSet D D.domain \ T.chart '' spliceCylinder)
    (e : hnormal.singularSet.Branch ≃ {b : hD.singularSet.Branch // b ≠ c})
    (he : ∀ b, hnormal.singularSet.branchCarrier b =
      hD.singularSet.branchCarrier (e b).1) :
    hnormal.singularSet.complexity < hD.singularSet.complexity :=
  (crossSeamResolutionDataOfTube R hnormal hGim hGD e he).complexity_lt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.complexity_lt_of_tube then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.complexity_lt_of_tube"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.complexity_lt_of_tube ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.complexity_lt_of_tube

def IsCrossSeamTubeProducer (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  ∀ (D : SingularTwoCell M) (BdM B : Set M) (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch), hD.singularSet.IsBoundaryBranch c →
    ∃ U : Set M, Nonempty (CrossSeamTubeData hD c U)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCrossSeamTubeProducer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCrossSeamTubeProducer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCrossSeamTubeProducer ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCrossSeamTubeProducer

end DifferentialGeometry.Topology.PiecewiseLinear
