/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FourSpokeDisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylinderSplice

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.Schoenflies

theorem fourSpokeIndexCases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i
  decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeIndexCases then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeIndexCases"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeIndexCases ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeIndexCases

def fourSpokeModelLeaf : Fin 4 → ℝ × ℝ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf

theorem mem_segment_zero_prod_iff {a p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) a ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p.1 = t * a.1 ∧ p.2 = t * a.2 := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨t, ht, by linarith, ?_, ?_⟩ <;> simp
  · rintro ⟨t, ht0, ht1, h1, h2⟩
    refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp [h1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_segment_zero_prod_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_segment_zero_prod_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_segment_zero_prod_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_segment_zero_prod_iff

theorem fourSpokeModelLeaf_ne_zero (i : Fin 4) : fourSpokeModelLeaf i ≠ (0 : ℝ × ℝ) := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    simp [fourSpokeModelLeaf, Prod.ext_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_ne_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_ne_zero

theorem fourSpokeModelLeaf_injective : Function.Injective fourSpokeModelLeaf := by
  intro i j hij
  revert hij
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
      norm_num [fourSpokeModelLeaf, Prod.ext_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeModelLeaf_injective

theorem segment_zero_fourSpokeModelLeaf_subset (i : Fin 4) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ⊆ spliceSquare := by
  intro p hp
  obtain ⟨t, ht0, ht1, h1, h2⟩ := mem_segment_zero_prod_iff.mp hp
  rw [mem_spliceSquare]
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
    · norm_num [fourSpokeModelLeaf] at h1 h2
      refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_subset

theorem eq_of_mem_frontier_spliceSquare_of_snd_eq_zero {p : ℝ × ℝ}
    (hp : p ∈ frontier spliceSquare) (h : p.2 = 0) : p = (1, 0) ∨ p = (-1, 0) := by
  rw [← spliceSquareBoundary_eq_frontier, mem_spliceSquareBoundary] at hp
  rcases hp.2 with h1 | h1 | h1 | h1
  · exact Or.inr (Prod.ext h1 h)
  · exact Or.inl (Prod.ext h1 h)
  · rw [h] at h1; norm_num at h1
  · rw [h] at h1; norm_num at h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_frontier_spliceSquare_of_snd_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_frontier_spliceSquare_of_snd_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_frontier_spliceSquare_of_snd_eq_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_of_mem_frontier_spliceSquare_of_snd_eq_zero

theorem segment_zero_fourSpokeModelLeaf_inter_frontier (i : Fin 4) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ∩ frontier spliceSquare =
      {fourSpokeModelLeaf i} := by
  rw [← spliceSquareBoundary_eq_frontier]
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨hp, hb⟩
    obtain ⟨t, ht0, ht1, h1, h2⟩ := mem_segment_zero_prod_iff.mp hp
    rw [mem_spliceSquareBoundary] at hb
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
      · change p.2 = (0 : ℝ)
        linarith
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (0 : ℝ)
        linarith
      · change p.2 = (1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (-1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
      · change p.2 = (0 : ℝ)
        linarith
    · norm_num [fourSpokeModelLeaf] at h1 h2
      simp only [fourSpokeModelLeaf]
      refine mem_singleton_iff.mpr (Prod.ext ?_ ?_)
      · change p.1 = (0 : ℝ)
        linarith
      · change p.2 = (-1 : ℝ)
        rcases hb.2 with h | h | h | h <;> linarith
  · rintro p rfl
    refine ⟨right_mem_segment ℝ _ _, ?_⟩
    rw [mem_spliceSquareBoundary]
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_⟩ <;> norm_num [fourSpokeModelLeaf, mem_spliceSquare]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter_frontier

theorem segment_zero_fourSpokeModelLeaf_inter {i j : Fin 4} (hij : i ≠ j) :
    segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) ∩
      segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf j) = {(0 : ℝ × ℝ)} := by
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨hp, hq⟩
    obtain ⟨t, ht0, ht1, h1, h2⟩ := mem_segment_zero_prod_iff.mp hp
    obtain ⟨s, hs0, hs1, k1, k2⟩ := mem_segment_zero_prod_iff.mp hq
    rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl <;>
      rcases fourSpokeIndexCases j with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hij
          | (norm_num [fourSpokeModelLeaf] at h1 h2 k1 k2
             exact mem_singleton_iff.mpr
               (Prod.ext (show p.1 = (0 : ℝ) by linarith) (show p.2 = (0 : ℝ) by linarith)))
  · rintro p rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.segment_zero_fourSpokeModelLeaf_inter

noncomputable def fourSpokePlaneEquiv : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokePlaneEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokePlaneEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokePlaneEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokePlaneEquiv

theorem isPLHomeomorphOn_fourSpokePlaneEquiv {S : Set (ℝ × ℝ)} (hS : IsPolyhedron S) :
    IsPLHomeomorphOn fourSpokePlaneEquiv S (fourSpokePlaneEquiv '' S) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hS
    ((isPiecewiseAffineOn_of_affine fourSpokePlaneEquiv.toLinearMap.toAffineMap
      isOpen_univ).mono_of_isPolyhedron hS (_root_.Set.subset_univ _))
    fourSpokePlaneEquiv.injective.injOn.bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokePlaneEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokePlaneEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokePlaneEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokePlaneEquiv

theorem image_segment_fourSpokePlaneEquiv (a b : ℝ × ℝ) :
    fourSpokePlaneEquiv '' segment ℝ a b =
      segment ℝ (fourSpokePlaneEquiv a) (fourSpokePlaneEquiv b) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    exact ⟨s, t, hs, ht, hst, by rw [map_add, map_smul, map_smul]⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, by rw [map_add, map_smul, map_smul]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_segment_fourSpokePlaneEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_segment_fourSpokePlaneEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_segment_fourSpokePlaneEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_segment_fourSpokePlaneEquiv

noncomputable def fourSpokeSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  fourSpokePlaneEquiv '' spliceSquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeSquare

noncomputable def fourSpokeCentre : EuclideanSpace ℝ (Fin 2) := fourSpokePlaneEquiv 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre

noncomputable def fourSpokeLeaf (i : Fin 4) : EuclideanSpace ℝ (Fin 2) :=
  fourSpokePlaneEquiv (fourSpokeModelLeaf i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf

noncomputable def fourSpokeArm (i : Fin 4) : Set (EuclideanSpace ℝ (Fin 2)) :=
  segment ℝ fourSpokeCentre (fourSpokeLeaf i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm

theorem fourSpokeArm_eq_image (i : Fin 4) :
    fourSpokeArm i = fourSpokePlaneEquiv '' segment ℝ (0 : ℝ × ℝ) (fourSpokeModelLeaf i) :=
  (image_segment_fourSpokePlaneEquiv _ _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_eq_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_eq_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_eq_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_eq_image

theorem fourSpokeCentre_ne_leaf (i : Fin 4) : fourSpokeCentre ≠ fourSpokeLeaf i := fun h =>
  (fourSpokeModelLeaf_ne_zero i) (fourSpokePlaneEquiv.injective h.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre_ne_leaf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre_ne_leaf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre_ne_leaf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeCentre_ne_leaf

theorem isPLBall_fourSpokeSquare : IsPLBall 2 fourSpokeSquare :=
  isPLBall_spliceSquare.of_isPLHomeomorphOn
    (isPLHomeomorphOn_fourSpokePlaneEquiv isPLBall_spliceSquare.isPolyhedron)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeSquare

theorem frontier_fourSpokeSquare :
    frontier fourSpokeSquare = fourSpokePlaneEquiv '' frontier spliceSquare := by
  simpa [fourSpokeSquare] using
    (fourSpokePlaneEquiv.toHomeomorph.image_frontier spliceSquare).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.frontier_fourSpokeSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.frontier_fourSpokeSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.frontier_fourSpokeSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.frontier_fourSpokeSquare

theorem isPLBall_fourSpokeArm (i : Fin 4) : IsPLBall 1 (fourSpokeArm i) :=
  isPLBall_segment (fourSpokeCentre_ne_leaf i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeArm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeArm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeArm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_fourSpokeArm

theorem isArcBetween_fourSpokeArm (i : Fin 4) :
    IsArcBetween (fourSpokeArm i) fourSpokeCentre (fourSpokeLeaf i) :=
  isArcBetween_segment (fourSpokeCentre_ne_leaf i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isArcBetween_fourSpokeArm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isArcBetween_fourSpokeArm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isArcBetween_fourSpokeArm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isArcBetween_fourSpokeArm

theorem fourSpokeArm_subset (i : Fin 4) : fourSpokeArm i ⊆ fourSpokeSquare := by
  rw [fourSpokeArm_eq_image, fourSpokeSquare]
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, segment_zero_fourSpokeModelLeaf_subset i hy, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_subset

theorem fourSpokeArm_inter_frontier (i : Fin 4) :
    fourSpokeArm i ∩ frontier fourSpokeSquare = {fourSpokeLeaf i} := by
  rw [fourSpokeArm_eq_image, frontier_fourSpokeSquare,
    ← Set.image_inter fourSpokePlaneEquiv.injective,
    segment_zero_fourSpokeModelLeaf_inter_frontier, _root_.Set.image_singleton]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter_frontier

theorem fourSpokeArm_inter {i j : Fin 4} (hij : i ≠ j) :
    fourSpokeArm i ∩ fourSpokeArm j = {fourSpokeCentre} := by
  rw [fourSpokeArm_eq_image, fourSpokeArm_eq_image,
    ← Set.image_inter fourSpokePlaneEquiv.injective,
    segment_zero_fourSpokeModelLeaf_inter hij, _root_.Set.image_singleton]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeArm_inter

theorem fourSpokeLeaf_mem_frontier (i : Fin 4) :
    fourSpokeLeaf i ∈ frontier fourSpokeSquare :=
  ((fourSpokeArm_inter_frontier i).symm.subset rfl).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_mem_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_mem_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_mem_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_mem_frontier

theorem fourSpokeLeaf_injective : Function.Injective fourSpokeLeaf := fun _ _ h =>
  fourSpokeModelLeaf_injective (fourSpokePlaneEquiv.injective h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_injective ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeLeaf_injective

theorem exists_isCutPair_fourSpokeSquare :
    ∃ A₁ A₂ : Set (EuclideanSpace ℝ (Fin 2)),
      IsCutPair (frontier fourSpokeSquare) (fourSpokeLeaf 0) (fourSpokeLeaf 2) A₁ A₂ ∧
        fourSpokeLeaf 1 ∈ A₁ ∧ fourSpokeLeaf 3 ∈ A₂ := by
  have hne02 : fourSpokeLeaf 0 ≠ fourSpokeLeaf 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (fourSpokeLeaf_injective h)
  obtain ⟨A, B, hcut, -, -⟩ := exists_isCutPair_isPLBall_of_isPLSphere_one
    isPLBall_fourSpokeSquare.isPLSphere_frontier (fourSpokeLeaf_mem_frontier 0)
    (fourSpokeLeaf_mem_frontier 2) hne02
  have hsep : ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin 2)),
      IsCutPair (frontier fourSpokeSquare) (fourSpokeLeaf 0) (fourSpokeLeaf 2) C₁ C₂ →
      fourSpokeLeaf 1 ∈ C₁ → fourSpokeLeaf 3 ∈ C₁ → False := by
    intro C₁ C₂ hc hm1 hm3
    have hmem : ∀ k : Fin 4, k ≠ 0 → k ≠ 2 → fourSpokeLeaf k ∈ C₁ →
        fourSpokeModelLeaf k ∈ fourSpokePlaneEquiv.symm ''
          (C₁ \ {fourSpokeLeaf 0, fourSpokeLeaf 2}) := by
      intro k hk0 hk2 hkC
      refine ⟨fourSpokeLeaf k, ⟨hkC, ?_⟩, ?_⟩
      · rintro (h | h)
        · exact hk0 (fourSpokeLeaf_injective h)
        · exact hk2 (fourSpokeLeaf_injective h)
      · exact fourSpokePlaneEquiv.symm_apply_apply _
    have hsub : fourSpokePlaneEquiv.symm '' (C₁ \ {fourSpokeLeaf 0, fourSpokeLeaf 2}) ⊆
        {p : ℝ × ℝ | 0 < p.2} ∪ {p : ℝ × ℝ | p.2 < 0} := by
      rintro p ⟨x, ⟨hxC, hx⟩, rfl⟩
      have hxJ : x ∈ frontier fourSpokeSquare := hc.fst_subset hxC
      rw [frontier_fourSpokeSquare] at hxJ
      obtain ⟨y, hy, rfl⟩ := hxJ
      rw [fourSpokePlaneEquiv.symm_apply_apply]
      rcases lt_trichotomy y.2 0 with h | h | h
      · exact Or.inr h
      · exfalso
        rcases eq_of_mem_frontier_spliceSquare_of_snd_eq_zero hy h with rfl | rfl
        · exact hx (Or.inl rfl)
        · exact hx (Or.inr rfl)
      · exact Or.inl h
    have hpre : IsPreconnected (fourSpokePlaneEquiv.symm ''
        (C₁ \ {fourSpokeLeaf 0, fourSpokeLeaf 2})) :=
      hc.fst.isPreconnected_diff.image _ fourSpokePlaneEquiv.symm.continuous.continuousOn
    have hd : Disjoint {p : ℝ × ℝ | 0 < p.2} {p : ℝ × ℝ | p.2 < 0} := by
      rw [Set.disjoint_left]
      intro p hp hp'
      have hp1 : (0 : ℝ) < p.2 := hp
      have hp2 : p.2 < 0 := hp'
      linarith
    have hone := IsPreconnected.subset_or_subset
      (isOpen_lt continuous_const continuous_snd) (isOpen_lt continuous_snd continuous_const)
      hd hsub hpre
    have h1 := hmem 1 (by decide) (by decide) hm1
    have h3 := hmem 3 (by decide) (by decide) hm3
    rcases hone with h | h
    · have hx : (0 : ℝ) < (fourSpokeModelLeaf 3).2 := h h3
      simp only [fourSpokeModelLeaf] at hx
      norm_num at hx
    · have hx : (fourSpokeModelLeaf 1).2 < 0 := h h1
      simp only [fourSpokeModelLeaf] at hx
      norm_num at hx
  have hmemAB : fourSpokeLeaf 1 ∈ A ∪ B := by
    rw [hcut.union_eq]; exact fourSpokeLeaf_mem_frontier 1
  have hmemAB' : fourSpokeLeaf 3 ∈ A ∪ B := by
    rw [hcut.union_eq]; exact fourSpokeLeaf_mem_frontier 3
  rcases hmemAB with h1 | h1
  · exact ⟨A, B, hcut, h1, hmemAB'.resolve_left fun h3 => hsep A B hcut h1 h3⟩
  · exact ⟨B, A, hcut.symm, h1, hmemAB'.resolve_right fun h3 => hsep B A hcut.symm h1 h3⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isCutPair_fourSpokeSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isCutPair_fourSpokeSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isCutPair_fourSpokeSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isCutPair_fourSpokeSquare

theorem exists_isPLHomeomorphOn_fourSpokeSquare :
    ∃ F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn F fourSpokeSquare fourSpokeSquare ∧
        EqOn F id (frontier fourSpokeSquare) ∧ ∀ i, _root_.Set.EqOn F id (fourSpokeArm i) := by
  obtain ⟨A₁, A₂, hcut, hv1, hv3⟩ := exists_isCutPair_fourSpokeSquare
  exact exists_isPLHomeomorphOn_of_fourSpokeDisk isPLBall_fourSpokeSquare
    isPLBall_fourSpokeSquare isPLBall_fourSpokeArm isPLBall_fourSpokeArm
    isArcBetween_fourSpokeArm isArcBetween_fourSpokeArm fourSpokeArm_subset
    fourSpokeArm_subset fourSpokeArm_inter_frontier fourSpokeArm_inter_frontier
    (fun _ _ h => fourSpokeArm_inter h) (fun _ _ h => fourSpokeArm_inter h) hcut hv1 hv3
    (π := 1) (g := id)
    isPLBall_fourSpokeSquare.isPLSphere_frontier.isPolyhedron.isPLHomeomorphOn_id
    (fun _ => rfl) (q := fun _ => id)
    (fun i => (isPLBall_fourSpokeArm i).isPolyhedron.isPLHomeomorphOn_id)
    (fun _ => rfl) (fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare

noncomputable def fourSpokeFlip :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (fourSpokePlaneEquiv.symm.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
    fourSpokePlaneEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip

def fourSpokeFlipPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm

theorem fourSpokeFlipPerm_zero : fourSpokeFlipPerm 0 = 1 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_zero ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_zero

theorem fourSpokeFlipPerm_one : fourSpokeFlipPerm 1 = 0 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_one

theorem fourSpokeFlipPerm_two : fourSpokeFlipPerm 2 = 3 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_two ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_two

theorem fourSpokeFlipPerm_three : fourSpokeFlipPerm 3 = 2 := by decide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_three ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlipPerm_three

theorem fourSpokeFlip_apply (x : ℝ × ℝ) :
    fourSpokeFlip (fourSpokePlaneEquiv x) = fourSpokePlaneEquiv (Prod.swap x) := by
  simp [fourSpokeFlip, Prod.swap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_apply

theorem image_swap_spliceSquare : Prod.swap '' spliceSquare = spliceSquare := by
  have hiff : ∀ p : ℝ × ℝ, Prod.swap p ∈ spliceSquare ↔ p ∈ spliceSquare := by
    intro p
    simp only [mem_spliceSquare, Prod.fst_swap, Prod.snd_swap]
    tauto
  refine Subset.antisymm ?_ fun p hp => ⟨Prod.swap p, (hiff p).mpr hp, Prod.swap_swap p⟩
  rintro x ⟨y, hy, rfl⟩
  exact (hiff y).mpr hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_swap_spliceSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_swap_spliceSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_swap_spliceSquare ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_swap_spliceSquare

theorem image_swap_segment (a b : ℝ × ℝ) :
    Prod.swap '' segment ℝ a b = segment ℝ (Prod.swap a) (Prod.swap b) := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, t, hs, ht, hst, rfl⟩, rfl⟩
    refine ⟨s, t, hs, ht, hst, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    refine ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_swap_segment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_swap_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_swap_segment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_swap_segment

theorem swap_fourSpokeModelLeaf (i : Fin 4) :
    Prod.swap (fourSpokeModelLeaf i) = fourSpokeModelLeaf (fourSpokeFlipPerm i) := by
  rcases fourSpokeIndexCases i with rfl | rfl | rfl | rfl
  · rw [fourSpokeFlipPerm_zero]; rfl
  · rw [fourSpokeFlipPerm_one]; rfl
  · rw [fourSpokeFlipPerm_two]; rfl
  · rw [fourSpokeFlipPerm_three]; rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.swap_fourSpokeModelLeaf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.swap_fourSpokeModelLeaf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.swap_fourSpokeModelLeaf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.swap_fourSpokeModelLeaf

theorem isPLHomeomorphOn_fourSpokeFlip {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS : IsPolyhedron S) : IsPLHomeomorphOn fourSpokeFlip S (fourSpokeFlip '' S) :=
  isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hS
    ((isPiecewiseAffineOn_of_affine fourSpokeFlip.toLinearMap.toAffineMap
      isOpen_univ).mono_of_isPolyhedron hS (_root_.Set.subset_univ _))
    fourSpokeFlip.injective.injOn.bijOn_image

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokeFlip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokeFlip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokeFlip ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLHomeomorphOn_fourSpokeFlip

theorem image_fourSpokeFlip_square : fourSpokeFlip '' fourSpokeSquare = fourSpokeSquare := by
  have hcomp : (fourSpokeFlip : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) ∘
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) =
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) ∘ Prod.swap :=
    funext fourSpokeFlip_apply
  rw [fourSpokeSquare, ← _root_.Set.image_comp, hcomp, _root_.Set.image_comp, image_swap_spliceSquare]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_square then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_square"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_square ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_square

theorem image_fourSpokeFlip_frontier :
    fourSpokeFlip '' frontier fourSpokeSquare = frontier fourSpokeSquare := by
  have h : fourSpokeFlip '' frontier fourSpokeSquare =
      frontier (fourSpokeFlip '' fourSpokeSquare) := by
    simpa using fourSpokeFlip.toHomeomorph.image_frontier fourSpokeSquare
  rw [h, image_fourSpokeFlip_square]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_frontier

theorem fourSpokeFlip_centre : fourSpokeFlip fourSpokeCentre = fourSpokeCentre := by
  rw [fourSpokeCentre, fourSpokeFlip_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_centre then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_centre"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_centre ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_centre

theorem fourSpokeFlip_leaf (i : Fin 4) :
    fourSpokeFlip (fourSpokeLeaf i) = fourSpokeLeaf (fourSpokeFlipPerm i) := by
  rw [fourSpokeLeaf, fourSpokeLeaf, fourSpokeFlip_apply, swap_fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_leaf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_leaf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_leaf ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.fourSpokeFlip_leaf

theorem image_fourSpokeFlip_arm (i : Fin 4) :
    fourSpokeFlip '' fourSpokeArm i = fourSpokeArm (fourSpokeFlipPerm i) := by
  have hcomp : (fourSpokeFlip : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) ∘
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) =
      (fourSpokePlaneEquiv : (ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)) ∘ Prod.swap :=
    funext fourSpokeFlip_apply
  have hzero : Prod.swap (0 : ℝ × ℝ) = 0 := rfl
  rw [fourSpokeArm_eq_image, fourSpokeArm_eq_image, ← _root_.Set.image_comp, hcomp, _root_.Set.image_comp,
    image_swap_segment, hzero, swap_fourSpokeModelLeaf]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_arm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_arm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_arm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.image_fourSpokeFlip_arm

theorem exists_isPLHomeomorphOn_fourSpokeSquare_flip :
    ∃ F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn F fourSpokeSquare fourSpokeSquare ∧
        _root_.Set.EqOn F fourSpokeFlip (frontier fourSpokeSquare) ∧
        ∀ i, _root_.Set.EqOn F fourSpokeFlip (fourSpokeArm i) := by
  obtain ⟨A₁, A₂, hcut, hv1, hv3⟩ := exists_isCutPair_fourSpokeSquare
  have hg : IsPLHomeomorphOn fourSpokeFlip (frontier fourSpokeSquare)
      (frontier fourSpokeSquare) := by
    have h := isPLHomeomorphOn_fourSpokeFlip
      isPLBall_fourSpokeSquare.isPLSphere_frontier.isPolyhedron
    rwa [image_fourSpokeFlip_frontier] at h
  have hq : ∀ i, IsPLHomeomorphOn fourSpokeFlip (fourSpokeArm i)
      (fourSpokeArm (fourSpokeFlipPerm i)) := by
    intro i
    have h := isPLHomeomorphOn_fourSpokeFlip (isPLBall_fourSpokeArm i).isPolyhedron
    rwa [image_fourSpokeFlip_arm] at h
  exact exists_isPLHomeomorphOn_of_fourSpokeDisk isPLBall_fourSpokeSquare
    isPLBall_fourSpokeSquare isPLBall_fourSpokeArm isPLBall_fourSpokeArm
    isArcBetween_fourSpokeArm isArcBetween_fourSpokeArm fourSpokeArm_subset
    fourSpokeArm_subset fourSpokeArm_inter_frontier fourSpokeArm_inter_frontier
    (fun _ _ h => fourSpokeArm_inter h) (fun _ _ h => fourSpokeArm_inter h) hcut hv1 hv3
    (π := fourSpokeFlipPerm) (g := fourSpokeFlip) hg fourSpokeFlip_leaf
    (q := fun _ => fourSpokeFlip) hq (fun _ => fourSpokeFlip_centre) (fun _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare_flip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare_flip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare_flip ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_fourSpokeSquare_flip

end DifferentialGeometry.Topology.PiecewiseLinear
