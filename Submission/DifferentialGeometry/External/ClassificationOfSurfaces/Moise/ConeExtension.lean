/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ClassificationOfSurfaces contributors
-/
import Submission.DifferentialGeometry.External.ClassificationOfSurfaces.Moise.FreeTriangleMove
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Separation.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Coning a subdivided triangle boundary

This file contains the finite geometry used in Moise Chapter 5.  The central observation is
that radial segments from an interior point of a convex set meet only as dictated by their
endpoints on the frontier.  It is the face-to-face lemma behind the cone extension of a PL map
on a triangle boundary.
-/

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace Moise

open _root_.Filter
open scoped _root_.Pointwise _root_.Topology

/-- A nondegenerate plane triangle has infinitely many interior points. -/
theorem IsTriangle.infinite_interior {C : Set Plane} (hC : IsTriangle C) :
    (interior C).Infinite := by
  obtain ⟨p, hp, rfl⟩ := hC
  have hspan : affineSpan ℝ (Set.range p) = ⊤ :=
    (hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp [Plane])
  have hne : (interior (convexHull ℝ (Set.range p))).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  obtain ⟨c, hc⟩ := hne
  have hp01 : p 0 ≠ p 1 := hp.injective.ne (by decide)
  let q := if p 0 = c then p 1 else p 0
  have hqc : q ≠ c := by
    dsimp [q]
    split_ifs with h
    · intro h1
      exact hp01 (h.trans h1.symm)
    · exact h
  have hqC : q ∈ convexHull ℝ (Set.range p) := by
    apply subset_convexHull ℝ
    dsimp [q]
    split_ifs <;> exact Set.mem_range_self _
  let m := midpoint ℝ c q
  have hmopen : m ∈ openSegment ℝ c q := midpoint_mem_openSegment c q
  have hm : m ∈ interior (convexHull ℝ (Set.range p)) :=
    (convex_convexHull ℝ (Set.range p)).openSegment_interior_self_subset_interior hc hqC hmopen
  have hmc : m ≠ c := by
    intro h
    have ht : (2 : ℝ)⁻¹ = 0 := by
      apply AffineMap.lineMap_injective ℝ hqc.symm
      simpa [m, midpoint] using h
    norm_num at ht
  exact (convex_convexHull ℝ (Set.range p)).interior.isPreconnected.infinite_of_nontrivial
    ⟨c, hc, m, hm, fun h => hmc h.symm⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.infinite_interior then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.infinite_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.infinite_interior ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.infinite_interior

theorem IsTriangle.convex {C : Set Plane} (hC : IsTriangle C) : Convex ℝ C := by
  obtain ⟨p, -, rfl⟩ := hC
  exact convex_convexHull ℝ (Set.range p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.convex then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.convex"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.convex ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.convex

theorem IsTriangle.isCompact {C : Set Plane} (hC : IsTriangle C) : IsCompact C := by
  obtain ⟨p, -, rfl⟩ := hC
  exact (Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.isCompact then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.isCompact ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.isCompact

theorem IsTriangle.frontier_nonempty {C : Set Plane} (hC : IsTriangle C) :
    (frontier C).Nonempty := by
  obtain ⟨p, -, rfl⟩ := hC
  apply nonempty_frontier_iff.mpr
  constructor
  · exact ⟨p 0, subset_convexHull ℝ _ (Set.mem_range_self 0)⟩
  · intro h
    have hb := ((Set.finite_range p).isCompact_convexHull (𝕜 := ℝ)).isBounded
    rw [h] at hb
    exact NormedSpace.unbounded_univ ℝ Plane hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.frontier_nonempty then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.frontier_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.frontier_nonempty ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.frontier_nonempty

/-- An interior cone point can be chosen away from any prescribed finite family of points. -/
theorem IsTriangle.exists_interior_not_mem_range {C : Set Plane} (hC : IsTriangle C)
    {ι : Type*} [Finite ι] (p : ι → Plane) :
    ∃ c ∈ interior C, c ∉ Set.range p := by
  exact hC.infinite_interior.exists_notMem_finite (Set.toFinite (Set.range p))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.exists_interior_not_mem_range then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.exists_interior_not_mem_range"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.exists_interior_not_mem_range ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.IsTriangle.exists_interior_not_mem_range

/-- Every point of a compact convex body lies on a radial segment from an interior point to the
frontier. -/
theorem exists_frontier_endpoint {S : Set Plane} (hS : Convex ℝ S) (hcompact : IsCompact S)
    {c x : Plane} (hc : c ∈ interior S) (hx : x ∈ S)
    (hfrontier : (frontier S).Nonempty) :
    ∃ y ∈ frontier S, x ∈ segment ℝ c y := by
  let T : Set Plane := (-c) +ᵥ S
  have hTconv : Convex ℝ T := hS.vadd (-c)
  have hTcompact : IsCompact T := hcompact.vadd (-c)
  have hzero : 0 ∈ interior T := by
    change 0 ∈ interior ((-c) +ᵥ S)
    rw [interior_vadd]
    exact ⟨c, hc, by simp⟩
  have hTnhds : T ∈ nhds 0 := mem_interior_iff_mem_nhds.mp hzero
  have hTabs : Absorbent ℝ T := absorbent_nhds_zero hTnhds
  have hTbounded : Bornology.IsVonNBounded ℝ T :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hTcompact.isBounded
  let v : Plane := x - c
  have hvT : v ∈ T := by
    exact ⟨x, hx, by simp [v, sub_eq_add_neg, add_comm]⟩
  by_cases hv : v = 0
  · obtain ⟨y, hy⟩ := hfrontier
    refine ⟨y, hy, ?_⟩
    have hxc : x = c := sub_eq_zero.mp hv
    rw [hxc]
    exact left_mem_segment ℝ c y
  · let g : ℝ := gauge T v
    have hgpos : 0 < g := (gauge_pos hTabs hTbounded).mpr hv
    have hgle : g ≤ 1 := gauge_le_one_of_mem hvT
    let y0 : Plane := g⁻¹ • v
    have hyGauge : gauge T y0 = 1 := by
      change gauge T (g⁻¹ • v) = 1
      rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le)]
      simp [g, hgpos.ne']
    have hy0 : y0 ∈ frontier T :=
      mem_frontier_of_gauge_eq_one hTconv (mem_of_mem_nhds hTnhds) hTabs hyGauge
    let y : Plane := c + y0
    have himage : (Homeomorph.addLeft c : Plane ≃ₜ Plane) '' T = S := by
      ext z
      simp only [Homeomorph.coe_addLeft, Set.mem_image, T, Set.mem_vadd_set]
      constructor
      · rintro ⟨w, ⟨q, hq, hqw⟩, rfl⟩
        simpa [← hqw] using hq
      · intro hz
        exact ⟨-c + z, ⟨z, hz, by simp⟩, by simp⟩
    have hy : y ∈ frontier S := by
      have hfront := (Homeomorph.addLeft c : Plane ≃ₜ Plane).image_frontier T
      rw [himage] at hfront
      rw [← hfront]
      exact ⟨y0, hy0, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [segment_eq_image_lineMap]
    refine ⟨g, ⟨hgpos.le, hgle⟩, ?_⟩
    simp [y, y0, v, AffineMap.lineMap_apply_module, g, hgpos.ne']
    module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.exists_frontier_endpoint then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.exists_frontier_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.exists_frontier_endpoint ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.exists_frontier_endpoint

/-- Two radial segments from an interior point of a convex set cannot share a non-central point
unless their frontier endpoints agree. -/
theorem eq_of_mem_segment_interior_frontier {S : Set Plane} (hS : Convex ℝ S)
    {c x y z : Plane} (hc : c ∈ interior S) (hx : x ∈ frontier S)
    (hy : y ∈ frontier S) (hzx : z ∈ segment ℝ c x) (hzy : z ∈ segment ℝ c y)
    (hzc : z ≠ c) : x = y := by
  have hcx : c ≠ x := by
    intro h
    subst x
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hx⟩
  have hcy : c ≠ y := by
    intro h
    subst y
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hy⟩
  have hzx' : Wbtw ℝ c z x := mem_segment_iff_wbtw.mp hzx
  have hzy' : Wbtw ℝ c z y := mem_segment_iff_wbtw.mp hzy
  have hzv : z - c ≠ 0 := sub_ne_zero.mpr hzc
  have hxyRay : SameRay ℝ (x -ᵥ c) (y -ᵥ c) :=
    (hzx'.sameRay_vsub_left.symm.trans hzy'.sameRay_vsub_left fun hz =>
      (hzv hz).elim)
  rcases wbtw_total_of_sameRay_vsub_left hxyRay with hxy | hyx
  · by_contra hne
    have hsbtw : Sbtw ℝ c x y := ⟨hxy, hcx.symm, hne⟩
    have hxopen : x ∈ openSegment ℝ c y := by
      rw [openSegment_eq_image_lineMap]
      exact hsbtw.mem_image_Ioo
    have hxint : x ∈ interior S :=
      hS.openSegment_interior_closure_subset_interior hc (frontier_subset_closure hy) hxopen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hxint, hx⟩
  · by_contra hne
    have hsbtw : Sbtw ℝ c y x := ⟨hyx, hcy.symm, fun h => hne h.symm⟩
    have hyopen : y ∈ openSegment ℝ c x := by
      rw [openSegment_eq_image_lineMap]
      exact hsbtw.mem_image_Ioo
    have hyint : y ∈ interior S :=
      hS.openSegment_interior_closure_subset_interior hc (frontier_subset_closure hx) hyopen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hyint, hy⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.eq_of_mem_segment_interior_frontier then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.eq_of_mem_segment_interior_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.eq_of_mem_segment_interior_frontier ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.eq_of_mem_segment_interior_frontier

/-- Coning preserves a face-to-face intersection when the base faces lie in the frontier of a
convex set and the cone point lies in its interior. -/
theorem convexHull_insert_inter_convexHull_insert {S A B : Set Plane}
    (hS : Convex ℝ S) (hA : A.Nonempty) (hB : B.Nonempty) {c : Plane}
    (hc : c ∈ interior S) (hAS : convexHull ℝ A ⊆ frontier S)
    (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (_root_.Insert.insert c A) ∩ convexHull ℝ (_root_.Insert.insert c B) =
      convexHull ℝ (_root_.Insert.insert c (A ∩ B)) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzA, hzB⟩
    rw [convexHull_insert hA, convexJoin_singleton_left] at hzA
    rw [convexHull_insert hB, convexJoin_singleton_left] at hzB
    simp only [Set.mem_iUnion] at hzA hzB
    obtain ⟨a, ha, hza⟩ := hzA
    obtain ⟨b, hb, hzb⟩ := hzB
    by_cases hzc : z = c
    · subst z
      exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · have hab : a = b := eq_of_mem_segment_interior_frontier hS hc
        (hAS ha) (hBS hb) hza hzb hzc
      have haInter : a ∈ convexHull ℝ (A ∩ B) := by
        rw [← hface]
        exact ⟨ha, hab ▸ hb⟩
      exact (convex_convexHull ℝ (_root_.Insert.insert c (A ∩ B))).segment_subset
        (subset_convexHull ℝ _ (Set.mem_insert _ _))
        (convexHull_mono (Set.subset_insert c (A ∩ B)) haInter) hza
  · intro z hz
    have hleft : _root_.Insert.insert c (A ∩ B) ⊆ _root_.Insert.insert c A := by
      rintro x (rfl | ⟨hx, -⟩)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ hx
    have hright : _root_.Insert.insert c (A ∩ B) ⊆ _root_.Insert.insert c B := by
      rintro x (rfl | ⟨-, hx⟩)
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ hx
    exact ⟨convexHull_mono hleft hz, convexHull_mono hright hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert

/-- The mixed cone/base face intersection used when exactly one face contains the cone point. -/
theorem convexHull_insert_inter_convexHull {S A B : Set Plane}
    (hS : Convex ℝ S) (hA : A.Nonempty) {c : Plane}
    (hc : c ∈ interior S) (hAS : convexHull ℝ A ⊆ frontier S)
    (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (_root_.Insert.insert c A) ∩ convexHull ℝ B = convexHull ℝ (A ∩ B) := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzA, hzB⟩
    rw [convexHull_insert hA, convexJoin_singleton_left] at hzA
    simp only [Set.mem_iUnion] at hzA
    obtain ⟨a, ha, hza⟩ := hzA
    have hzFrontier : z ∈ frontier S := hBS hzB
    have hzc : z ≠ c := by
      intro h
      subst z
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hzFrontier⟩
    have haz : a = z := eq_of_mem_segment_interior_frontier hS hc
      (hAS ha) hzFrontier hza (right_mem_segment ℝ c z) hzc
    rw [← hface]
    exact ⟨haz ▸ ha, hzB⟩
  · intro z hz
    have hzA : z ∈ convexHull ℝ A := convexHull_mono Set.inter_subset_left hz
    have hzB : z ∈ convexHull ℝ B := convexHull_mono Set.inter_subset_right hz
    exact ⟨convexHull_mono (Set.subset_insert c A) hzA, hzB⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull

/-- Cone/cone intersection, including the degenerate case where one base face is empty. -/
theorem convexHull_insert_inter_convexHull_insert' {S A B : Set Plane}
    (hS : Convex ℝ S) {c : Plane} (hc : c ∈ interior S)
    (hAS : convexHull ℝ A ⊆ frontier S) (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (_root_.Insert.insert c A) ∩ convexHull ℝ (_root_.Insert.insert c B) =
      convexHull ℝ (_root_.Insert.insert c (A ∩ B)) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hcone : convexHull ℝ (_root_.Insert.insert c (∅ : Set Plane)) = {c} := by simp
    rw [hcone]
    simp only [Set.empty_inter, hcone]
    apply Set.Subset.antisymm
    · exact Set.inter_subset_left
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨rfl, subset_convexHull ℝ _ (Set.mem_insert _ _)⟩
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have hcone : convexHull ℝ (_root_.Insert.insert c (∅ : Set Plane)) = {c} := by simp
    rw [hcone]
    simp only [Set.inter_empty, hcone]
    apply Set.Subset.antisymm
    · exact Set.inter_subset_right
    · intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨subset_convexHull ℝ _ (Set.mem_insert _ _), rfl⟩
  exact convexHull_insert_inter_convexHull_insert hS hA hB hc hAS hBS hface

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert' then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert'"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert' ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull_insert'

/-- Cone/base intersection, including an empty cone base. -/
theorem convexHull_insert_inter_convexHull' {S A B : Set Plane}
    (hS : Convex ℝ S) {c : Plane} (hc : c ∈ interior S)
    (hAS : convexHull ℝ A ⊆ frontier S) (hBS : convexHull ℝ B ⊆ frontier S)
    (hface : convexHull ℝ A ∩ convexHull ℝ B = convexHull ℝ (A ∩ B)) :
    convexHull ℝ (_root_.Insert.insert c A) ∩ convexHull ℝ B = convexHull ℝ (A ∩ B) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have hcone : convexHull ℝ (_root_.Insert.insert c (∅ : Set Plane)) = {c} := by simp
    rw [hcone]
    simp only [Set.empty_inter, convexHull_empty]
    ext z
    constructor
    · rintro ⟨hz, hzB⟩
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hBS hzB⟩
    · simp
  exact convexHull_insert_inter_convexHull hS hA hc hAS hBS hface

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull' then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull'"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull' ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.convexHull_insert_inter_convexHull'

/-- An interior point and the endpoints of a nondegenerate frontier segment are not collinear. -/
theorem not_collinear_interior_frontier_segment {S : Set Plane} (hS : Convex ℝ S)
    {c a b : Plane} (hc : c ∈ interior S) (ha : a ∈ frontier S)
    (hb : b ∈ frontier S) (hab : a ≠ b) (hsegment : segment ℝ a b ⊆ frontier S) :
    ¬Collinear ℝ ({c, a, b} : Set Plane) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hcab | habc | hcba
  · have hac : a ≠ c := by
      intro h
      subst a
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, ha⟩
    have hs : Sbtw ℝ c a b := ⟨hcab, hac, hab⟩
    have haOpen : a ∈ openSegment ℝ c b := by
      rw [openSegment_eq_image_lineMap]
      exact hs.mem_image_Ioo
    have haInt := hS.openSegment_interior_closure_subset_interior hc
      (frontier_subset_closure hb) haOpen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨haInt, ha⟩
  · have hba : b ≠ a := hab.symm
    have hbc : b ≠ c := by
      intro h
      subst b
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hb⟩
    have hs : Sbtw ℝ a b c := ⟨habc, hba, hbc⟩
    have hbOpen : b ∈ openSegment ℝ a c := by
      rw [openSegment_eq_image_lineMap]
      exact hs.mem_image_Ioo
    have hbInt := hS.openSegment_closure_interior_subset_interior
      (frontier_subset_closure ha) hc hbOpen
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hbInt, hb⟩
  · have hcFrontier : c ∈ frontier S := hsegment (Wbtw.mem_segment hcba.symm)
    exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, hcFrontier⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.not_collinear_interior_frontier_segment then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.not_collinear_interior_frontier_segment"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.not_collinear_interior_frontier_segment ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.not_collinear_interior_frontier_segment

/-- Adding an interior cone point to at most two affinely independent frontier vertices preserves
affine independence. -/
theorem affineIndependent_insert_interior_of_card_le_two {S : Set Plane} (hS : Convex ℝ S)
    {A : Finset Plane} (hAcard : A.card ≤ 2)
    (hAI : AffineIndependent ℝ ((↑) : A → Plane))
    (hAS : convexHull ℝ (A : Set Plane) ⊆ frontier S) {c : Plane}
    (hc : c ∈ interior S) :
    AffineIndependent ℝ ((↑) : ↥(_root_.Insert.insert c A) → Plane) := by
  interval_cases hcard : A.card
  · have hAempty : A = ∅ := Finset.card_eq_zero.mp hcard
    subst A
    simp only [Finset.insert_empty]
    exact affineIndependent_of_subsingleton ℝ _
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    have haFrontier : a ∈ frontier S := by
      apply hAS
      simpa only [Finset.coe_singleton] using
        subset_convexHull ℝ ({a} : Set Plane) (Set.mem_singleton a)
    have hca : c ≠ a := by
      intro h
      subst a
      exact (disjoint_interior_frontier (s := S)).le_bot ⟨hc, haFrontier⟩
    have hpair : AffineIndependent ℝ ![c, a] := affineIndependent_of_ne (k := ℝ) hca
    apply affineIndependent_finset_coe hpair
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have haFrontier : a ∈ frontier S := by
      apply hAS
      exact subset_convexHull ℝ (↑({a, b} : Finset Plane) : Set Plane) (by simp)
    have hbFrontier : b ∈ frontier S := by
      apply hAS
      exact subset_convexHull ℝ (↑({a, b} : Finset Plane) : Set Plane) (by simp)
    have hsegment : segment ℝ a b ⊆ frontier S := by
      simpa [convexHull_pair] using hAS
    have htriple : AffineIndependent ℝ ![c, a, b] :=
      affineIndependent_iff_not_collinear_set.mpr
        (not_collinear_interior_frontier_segment hS hc haFrontier hbFrontier hab hsegment)
    apply affineIndependent_finset_coe htriple
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_insert_interior_of_card_le_two then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_insert_interior_of_card_le_two"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_insert_interior_of_card_le_two ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.affineIndependent_insert_interior_of_card_le_two

namespace PlaneComplex

variable (K : PlaneComplex)

/-- Vertices which actually occur in the geometric support.  Passing to this subtype removes
irrelevant vertices that a `PlaneComplex` is allowed to carry. -/
abbrev ActiveVertex := {v : K.Vertex // K.position v ∈ K.support}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.ActiveVertex then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.ActiveVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.ActiveVertex ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.ActiveVertex

noncomputable instance activeVertexFintype : Fintype K.ActiveVertex := Fintype.ofFinite _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeVertexFintype then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeVertexFintype"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeVertexFintype ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeVertexFintype

/-- The `activeEmbedding` declaration. -/
def activeEmbedding : K.ActiveVertex ↪ K.Vertex := Function.Embedding.subtype _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeEmbedding then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeEmbedding ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeEmbedding

/-- The `activeSimplexes` declaration. -/
noncomputable def activeSimplexes : Finset (Finset K.ActiveVertex) :=
  Finset.univ.filter fun s => s.map K.activeEmbedding ∈ K.simplexes

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeSimplexes then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeSimplexes"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeSimplexes ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.activeSimplexes

@[simp] theorem mem_activeSimplexes {s : Finset K.ActiveVertex} :
    s ∈ K.activeSimplexes ↔ s.map K.activeEmbedding ∈ K.simplexes := by
  simp [activeSimplexes]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_activeSimplexes then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_activeSimplexes"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_activeSimplexes ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_activeSimplexes

theorem active_position_image (s : Finset K.ActiveVertex) :
    (fun v : K.ActiveVertex => K.position v.1) '' (s : Set K.ActiveVertex) =
      K.position '' ((s.map K.activeEmbedding : Finset K.Vertex) : Set K.Vertex) := by
  ext x
  simp [activeEmbedding]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_position_image then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_position_image"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_position_image ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_position_image

/-- Delete all unused vertices without changing the support or any face geometry. -/
noncomputable def active : PlaneComplex where
  Vertex := K.ActiveVertex
  position := fun v => K.position v.1
  position_injective := fun v w h => Subtype.ext (K.position_injective h)
  simplexes := K.activeSimplexes
  nonempty_of_mem := by
    intro s hs
    have hne := K.nonempty_of_mem _ (K.mem_activeSimplexes.mp hs)
    simpa using hne
  card_le_three := by
    intro s hs
    rw [← Finset.card_map K.activeEmbedding]
    exact K.card_le_three _ (K.mem_activeSimplexes.mp hs)
  down_closed := by
    intro s hs t hts htne
    apply K.mem_activeSimplexes.mpr
    apply K.down_closed _ (K.mem_activeSimplexes.mp hs)
    · exact Finset.map_subset_map.mpr hts
    · simpa using htne
  affineIndependent := by
    intro s hs
    have h := K.affineIndependent (s.map K.activeEmbedding) (K.mem_activeSimplexes.mp hs)
    let e : s ↪ (s.map K.activeEmbedding) :=
      { toFun := fun v => ⟨v.1.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          have hval : v.1.1 = w.1.1 :=
            congrArg (fun q : (s.map K.activeEmbedding) => q.1) hvw
          exact Subtype.ext (Subtype.ext hval) }
    exact h.comp_embedding e
  face_inter := by
    intro s hs t ht
    have h := K.face_inter (s.map K.activeEmbedding) (K.mem_activeSimplexes.mp hs)
      (t.map K.activeEmbedding) (K.mem_activeSimplexes.mp ht)
    rw [← Finset.map_inter] at h
    simpa only [K.active_position_image] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active

theorem active_cellCarrier (s : Finset K.ActiveVertex) :
    (active K).cellCarrier s = K.cellCarrier (s.map K.activeEmbedding) := by
  exact congrArg (convexHull ℝ) (K.active_position_image s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_cellCarrier then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_cellCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_cellCarrier ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_cellCarrier

theorem active_support : (active K).support = K.support := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s.map K.activeEmbedding, K.mem_activeSimplexes.mp hs,
      (K.active_cellCarrier s).le hxs⟩
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    let t : Finset K.ActiveVertex := Finset.univ.filter fun v => v.1 ∈ s
    have hmap : t.map K.activeEmbedding = s := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact (Finset.mem_filter.mp hw).2
      · intro v hv
        have hvCarrier : K.position v ∈ K.cellCarrier s :=
          subset_convexHull ℝ _ ⟨v, hv, rfl⟩
        let w : K.ActiveVertex := ⟨v, K.cellCarrier_subset_support hs hvCarrier⟩
        exact Finset.mem_map.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    have ht : t ∈ K.activeSimplexes := K.mem_activeSimplexes.mpr (hmap ▸ hs)
    refine ⟨t, ht, ?_⟩
    rw [K.active_cellCarrier, hmap]
    exact hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_support then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_support"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_support ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_support

/-- Removing unused vertices preserves purity of a two-dimensional complex. -/
theorem IsPure2.active (hpure : K.IsPure2) : (active K).IsPure2 := by
  intro s hs
  obtain ⟨t, ht, hst, htcard⟩ := hpure (s.map K.activeEmbedding)
    (K.mem_activeSimplexes.mp hs)
  let t' := (Finset.univ : Finset K.ActiveVertex).filter fun v => v.1 ∈ t
  have hmap : t'.map K.activeEmbedding = t := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro v hv
      have hvCarrier : K.position v ∈ K.cellCarrier t :=
        subset_convexHull ℝ _ ⟨v, hv, rfl⟩
      let w : K.ActiveVertex := ⟨v, K.cellCarrier_subset_support ht hvCarrier⟩
      exact Finset.mem_map.mpr
        ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨t', K.mem_activeSimplexes.mpr (hmap ▸ ht), ?_, ?_⟩
  · intro v hv
    have hvmap : K.activeEmbedding v ∈ t :=
      hst (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvmap⟩
  · have hcardmap : (t'.map K.activeEmbedding).card = t'.card :=
      Finset.card_map K.activeEmbedding
    rw [hmap, htcard] at hcardmap
    exact hcardmap.symm

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.active then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.active"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.active ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.active

/-- A plane complex supported on the frontier of a closed set has no two-dimensional face. -/
theorem card_le_two_of_support_eq_frontier {S : Set Plane} (hSclosed : IsClosed S)
    (hsupport : K.support = frontier S) {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    s.card ≤ 2 := by
  by_contra hnot
  have hcard : s.card = 3 := by
    have hle := K.card_le_three s hs
    omega
  have hspan : affineSpan ℝ (Set.range (fun v : s => K.position v)) = ⊤ :=
    ((K.affineIndependent s hs).affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by
      simp [hcard, Plane])
  have hne : (interior (K.cellCarrier s)).Nonempty := by
    rw [PlaneComplex.cellCarrier]
    have himage : Set.range (fun v : s => K.position v) =
        K.position '' (s : Set K.Vertex) := by
      ext x
      simp
    rw [← himage]
    exact interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hsubset : interior (K.cellCarrier s) ⊆ interior (frontier S) :=
    interior_mono ((K.cellCarrier_subset_support hs).trans_eq hsupport)
  rw [interior_frontier hSclosed] at hsubset
  exact hne.not_subset_empty hsubset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.card_le_two_of_support_eq_frontier then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.card_le_two_of_support_eq_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.card_le_two_of_support_eq_frontier ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.card_le_two_of_support_eq_frontier

theorem active_subdivides_left {L K : PlaneComplex} (h : L.Subdivides K) :
    (active L).Subdivides K := by
  constructor
  · rw [L.active_support, h.1]
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h.2 (s.map L.activeEmbedding) (L.mem_activeSimplexes.mp hs)
    exact ⟨t, ht, (L.active_cellCarrier s).le.trans hst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_subdivides_left then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_subdivides_left"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_subdivides_left ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.active_subdivides_left

/-- Vertices which occur in at least one abstract face.  Unlike `ActiveVertex`, this removes a
vertex whose geometric position happens to lie in the support without being part of any face. -/
abbrev UsedVertex := {v : K.Vertex // ∃ s ∈ K.simplexes, v ∈ s}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.UsedVertex then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.UsedVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.UsedVertex ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.UsedVertex

noncomputable instance usedVertexFintype : Fintype K.UsedVertex := Fintype.ofFinite _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedVertexFintype then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedVertexFintype"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedVertexFintype ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedVertexFintype

/-- The `usedEmbedding` declaration. -/
def usedEmbedding : K.UsedVertex ↪ K.Vertex := Function.Embedding.subtype _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedEmbedding then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedEmbedding ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedEmbedding

/-- The `usedSimplexes` declaration. -/
noncomputable def usedSimplexes : Finset (Finset K.UsedVertex) :=
  Finset.univ.filter fun s => s.map K.usedEmbedding ∈ K.simplexes

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedSimplexes then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedSimplexes"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedSimplexes ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.usedSimplexes

@[simp] theorem mem_usedSimplexes {s : Finset K.UsedVertex} :
    s ∈ K.usedSimplexes ↔ s.map K.usedEmbedding ∈ K.simplexes := by
  simp [usedSimplexes]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_usedSimplexes then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_usedSimplexes"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_usedSimplexes ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_usedSimplexes

theorem used_position_image (s : Finset K.UsedVertex) :
    (fun v : K.UsedVertex => K.position v.1) '' (s : Set K.UsedVertex) =
      K.position '' ((s.map K.usedEmbedding : Finset K.Vertex) : Set K.Vertex) := by
  ext x
  simp [usedEmbedding]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_position_image then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_position_image"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_position_image ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_position_image

/-- Delete vertices unused by every face, without changing the represented complex. -/
noncomputable def used : PlaneComplex where
  Vertex := K.UsedVertex
  position := fun v => K.position v.1
  position_injective := fun v w h => Subtype.ext (K.position_injective h)
  simplexes := K.usedSimplexes
  nonempty_of_mem := by
    intro s hs
    have hne := K.nonempty_of_mem _ (K.mem_usedSimplexes.mp hs)
    simpa using hne
  card_le_three := by
    intro s hs
    rw [← Finset.card_map K.usedEmbedding]
    exact K.card_le_three _ (K.mem_usedSimplexes.mp hs)
  down_closed := by
    intro s hs t hts htne
    apply K.mem_usedSimplexes.mpr
    apply K.down_closed _ (K.mem_usedSimplexes.mp hs)
    · exact Finset.map_subset_map.mpr hts
    · simpa using htne
  affineIndependent := by
    intro s hs
    have h := K.affineIndependent (s.map K.usedEmbedding) (K.mem_usedSimplexes.mp hs)
    let e : s ↪ (s.map K.usedEmbedding) :=
      { toFun := fun v => ⟨v.1.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          have hval : v.1.1 = w.1.1 := congrArg (fun q => q.1) hvw
          exact Subtype.ext (Subtype.ext hval) }
    exact h.comp_embedding e
  face_inter := by
    intro s hs t ht
    have h := K.face_inter (s.map K.usedEmbedding) (K.mem_usedSimplexes.mp hs)
      (t.map K.usedEmbedding) (K.mem_usedSimplexes.mp ht)
    rw [← Finset.map_inter] at h
    simpa only [K.used_position_image] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used

theorem used_cellCarrier (s : Finset K.UsedVertex) :
    (used K).cellCarrier s = K.cellCarrier (s.map K.usedEmbedding) := by
  exact congrArg (convexHull ℝ) (K.used_position_image s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_cellCarrier then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_cellCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_cellCarrier ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_cellCarrier

theorem used_support : (used K).support = K.support := by
  apply Set.Subset.antisymm
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s.map K.usedEmbedding, K.mem_usedSimplexes.mp hs,
      (K.used_cellCarrier s).le hxs⟩
  · intro x hx
    rw [PlaneComplex.support] at hx ⊢
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hxs⟩ := hx
    let t : Finset K.UsedVertex := Finset.univ.filter fun v => v.1 ∈ s
    have hmap : t.map K.usedEmbedding = s := by
      apply Finset.Subset.antisymm
      · intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
        exact (Finset.mem_filter.mp hw).2
      · intro v hv
        let w : K.UsedVertex := ⟨v, s, hs, hv⟩
        exact Finset.mem_map.mpr
          ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
    have ht : t ∈ K.usedSimplexes := K.mem_usedSimplexes.mpr (hmap ▸ hs)
    refine ⟨t, ht, ?_⟩
    rw [K.used_cellCarrier, hmap]
    exact hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_support then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_support"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_support ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_support

theorem used_vertex_face (v : K.UsedVertex) :
    ({v} : Finset (used K).Vertex) ∈ (used K).simplexes := by
  apply K.mem_usedSimplexes.mpr
  obtain ⟨s, hs, hvs⟩ := v.2
  apply K.down_closed s hs {v.1}
  · simpa [usedEmbedding] using hvs
  · exact Finset.singleton_nonempty _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_vertex_face then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_vertex_face"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_vertex_face ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_vertex_face

/-- Every face of a complex is represented by an identical geometric face after unused vertices
are removed. -/
theorem exists_used_face_eq (s : Finset K.Vertex) (hs : s ∈ K.simplexes) :
    ∃ t : Finset (used K).Vertex, t ∈ (used K).simplexes ∧
      t.map K.usedEmbedding = s ∧ (used K).cellCarrier t = K.cellCarrier s := by
  classical
  let t : Finset K.UsedVertex := Finset.univ.filter fun v => v.1 ∈ s
  have hmap : t.map K.usedEmbedding = s := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro v hv
      let w : K.UsedVertex := ⟨v, s, hs, hv⟩
      exact Finset.mem_map.mpr
        ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨t, K.mem_usedSimplexes.mpr (hmap ▸ hs), hmap, ?_⟩
  rw [K.used_cellCarrier, hmap]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_used_face_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_used_face_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_used_face_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_used_face_eq

/-- Removing vertices unused by every face preserves two-dimensional purity. -/
theorem IsPure2.used (hpure : K.IsPure2) : (used K).IsPure2 := by
  intro s hs
  obtain ⟨t, ht, hst, htcard⟩ := hpure (s.map K.usedEmbedding)
    (K.mem_usedSimplexes.mp hs)
  let t' : Finset K.UsedVertex := Finset.univ.filter fun v => v.1 ∈ t
  have hmap : t'.map K.usedEmbedding = t := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_filter.mp hw).2
    · intro v hv
      let w : K.UsedVertex := ⟨v, t, ht, hv⟩
      exact Finset.mem_map.mpr
        ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩
  refine ⟨t', K.mem_usedSimplexes.mpr (hmap ▸ ht), ?_, ?_⟩
  · intro v hv
    have hvmap : K.usedEmbedding v ∈ t :=
      hst (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvmap⟩
  · have hcardmap : (t'.map K.usedEmbedding).card = t'.card :=
      Finset.card_map K.usedEmbedding
    rw [hmap, htcard] at hcardmap
    exact hcardmap.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.used then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.used"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.used ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.IsPure2.used

theorem used_subdivides_left {L K : PlaneComplex} (h : L.Subdivides K) :
    (used L).Subdivides K := by
  constructor
  · rw [L.used_support, h.1]
  · intro s hs
    obtain ⟨t, ht, hst⟩ := h.2 (s.map L.usedEmbedding) (L.mem_usedSimplexes.mp hs)
    exact ⟨t, ht, (L.used_cellCarrier s).le.trans hst⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_subdivides_left then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_subdivides_left"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_subdivides_left ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.used_subdivides_left

/-- Values prescribed on an affinely independent family extend to an affine map of the plane. -/
theorem exists_affineMap_eqOn_affineIndependent {ι : Type*} [Nonempty ι]
    (p q : ι → Plane) (hp : AffineIndependent ℝ p) :
    ∃ g : Plane →ᵃ[ℝ] Plane, ∀ i, g (p i) = q i := by
  classical
  let e : ι ≃ Set.range p := Equiv.ofBijective
    (fun i => ⟨p i, Set.mem_range_self i⟩)
    ⟨fun i j h => hp.injective (congrArg Subtype.val h), by
      rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  have hRange : AffineIndependent ℝ ((↑) : Set.range p → Plane) := by
    apply (affineIndependent_equiv e).mp
    exact hp
  obtain ⟨T, hsub, hTI, hspan⟩ :=
    exists_subset_affineIndependent_affineSpan_eq_top hRange
  let b : AffineBasis T ℝ Plane :=
    ⟨((↑) : T → Plane), hTI, by
      have hrange : Set.range ((↑) : T → Plane) = T := by ext x; simp
      rw [hrange]
      exact hspan⟩
  let embed : ι → T := fun i => ⟨p i, hsub (Set.mem_range_self i)⟩
  let Q : T → Plane := fun z =>
    if hz : (z : Plane) ∈ Set.range p then q (e.symm ⟨z, hz⟩) else 0
  let i0 : T := embed (Classical.choice inferInstance)
  let l : Plane →ₗ[ℝ] Plane :=
    (b.basisOf i0).constr ℝ (fun j => Q j - Q i0)
  let g : Plane →ᵃ[ℝ] Plane :=
    { toFun := fun x => l (x - b i0) + Q i0
      linear := l
      map_vadd' := by
        intro x v
        simp only [vadd_eq_add, map_add, map_sub]
        module }
  have hgBasis (i : T) : g (b i) = Q i := by
    by_cases hi : i = i0
    · subst i
      simp [g]
    · let j : {j : T // j ≠ i0} := ⟨i, hi⟩
      change l (b i - b i0) + Q i0 = Q i
      have hl : l (b i - b i0) = Q i - Q i0 := by
        have hbasis : (b.basisOf i0) j = b i - b i0 := by
          exact b.basisOf_apply i0 j
        rw [← hbasis]
        rw [Module.Basis.constr_basis]
      rw [hl]
      abel
  refine ⟨g, fun i => ?_⟩
  have hb : b (embed i) = p i := rfl
  rw [← hb, hgBasis]
  simp only [Q, embed, dif_pos (Set.mem_range_self i)]
  exact congrArg q (e.symm_apply_apply i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_affineMap_eqOn_affineIndependent then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_affineMap_eqOn_affineIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_affineMap_eqOn_affineIndependent ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_affineMap_eqOn_affineIndependent

/-- Map a one-dimensional complex by a function affine on every face and injective on its
support. -/
noncomputable def mapGraph (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support)
    (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) : PlaneComplex where
  Vertex := K.Vertex
  position := f ∘ K.position
  position_injective := fun v w h => K.position_injective
    (hinj (hvertex v) (hvertex w) h)
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := fun s hs => (hgraph s hs).trans (by omega)
  down_closed := K.down_closed
  affineIndependent := by
    intro s hs
    let A : Finset Plane := s.image (f ∘ K.position)
    have hAcard : A.card ≤ 2 := by
      rw [Finset.card_image_of_injective]
      · exact hgraph s hs
      · intro v w h
        exact K.position_injective (hinj (hvertex v) (hvertex w) h)
    have hAI := affineIndependent_finset_of_card_le_two A hAcard
    let e : s ↪ A :=
      { toFun := fun v => ⟨f (K.position v), Finset.mem_image.mpr ⟨v, v.2, rfl⟩⟩
        inj' := by
          intro v w hvw
          have hval : f (K.position v.1) = f (K.position w.1) :=
            congrArg (fun q : A => q.1) hvw
          exact Subtype.ext (K.position_injective
            (hinj (hvertex v.1) (hvertex w.1) hval)) }
    exact hAI.comp_embedding e
  face_inter := by
    intro s hs t ht
    have hcarrier (u : Finset K.Vertex) (hu : u ∈ K.simplexes) :
        convexHull ℝ ((f ∘ K.position) '' (u : Set K.Vertex)) =
          f '' K.cellCarrier u := by
      rw [Set.image_comp]
      exact IsAffineOn.image_convexHull (haffine u hu)
    rw [hcarrier s hs, hcarrier t ht]
    rw [← hinj.image_inter (K.cellCarrier_subset_support hs)
      (K.cellCarrier_subset_support ht)]
    have hface : K.cellCarrier s ∩ K.cellCarrier t = K.cellCarrier (s ∩ t) := by
      simpa [PlaneComplex.cellCarrier] using K.face_inter s hs t ht
    rw [hface]
    by_cases hne : (s ∩ t).Nonempty
    · exact (hcarrier (s ∩ t) (K.down_closed s hs _ Finset.inter_subset_left hne)).symm
    · have hempty : s ∩ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, PlaneComplex.cellCarrier]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph

theorem mapGraph_cellCarrier (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support) (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    (K.mapGraph f hvertex hinj hgraph haffine).cellCarrier s = f '' K.cellCarrier s := by
  change convexHull ℝ ((f ∘ K.position) '' (s : Set K.Vertex)) = _
  rw [Set.image_comp]
  exact IsAffineOn.image_convexHull (haffine s hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_cellCarrier then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_cellCarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_cellCarrier ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_cellCarrier

theorem mapGraph_support (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support) (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s)) :
    (K.mapGraph f hvertex hinj hgraph haffine).support = f '' K.support := by
  rw [PlaneComplex.support, PlaneComplex.support]
  ext x
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨s, hs, hxs⟩
    rw [K.mapGraph_cellCarrier f hvertex hinj hgraph haffine hs] at hxs
    obtain ⟨y, hy, rfl⟩ := hxs
    exact ⟨y, ⟨s, hs, hy⟩, rfl⟩
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    rw [K.mapGraph_cellCarrier f hvertex hinj hgraph haffine hs]
    exact ⟨y, hy, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_support then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_support"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_support ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_support

theorem mapGraph_baryEval_eq (f : Plane → Plane)
    (hvertex : ∀ v, K.position v ∈ K.support) (hinj : Set.InjOn f K.support)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (haffine : ∀ s ∈ K.simplexes, IsAffineOn f (K.cellCarrier s))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) {z : K.Vertex → ℝ}
    (hzsupp : ∀ v ∉ s, z v = 0) (hz0 : ∀ v, 0 ≤ z v)
    (hzsum : ∑ v, z v = 1) :
    (K.mapGraph f hvertex hinj hgraph haffine).baryEval z = f (K.baryEval z) := by
  obtain ⟨g, hfg⟩ := haffine s hs
  have hsum : ∑ v ∈ s, z v = 1 := by
    rw [← K.sum_eq_sum_of_support hzsupp]
    exact hzsum
  have hsource : K.baryEval z = s.affineCombination ℝ K.position z := by
    rw [s.affineCombination_eq_linear_combination K.position z hsum]
    exact K.baryEval_eq_sum_of_support hzsupp
  have htarget : (K.mapGraph f hvertex hinj hgraph haffine).baryEval z =
      s.affineCombination ℝ (f ∘ K.position) z := by
    rw [s.affineCombination_eq_linear_combination (f ∘ K.position) z hsum]
    change (∑ v, z v • f (K.position v)) = ∑ v ∈ s, z v • f (K.position v)
    exact (Finset.sum_subset (Finset.subset_univ s)
      (fun v _ hv => by rw [hzsupp v hv, zero_smul])).symm
  rw [htarget, hsource]
  have hfgSource : f (s.affineCombination ℝ K.position z) =
      g (s.affineCombination ℝ K.position z) := by
    rw [← hsource]
    exact hfg (K.baryEval_mem_cellCarrier hzsupp hz0 hzsum)
  rw [hfgSource, s.map_affineCombination K.position z hsum g]
  have hfg' : ∀ v ∈ s, f (K.position v) = g (K.position v) := by
    intro v hv
    exact hfg (subset_convexHull ℝ _ ⟨v, hv, rfl⟩)
  have hcomb : s.affineCombination ℝ (f ∘ K.position) z =
      s.affineCombination ℝ (g ∘ K.position) z := by
    apply Finset.affineCombination_congr s (fun _ _ => rfl)
    intro v hv
    exact hfg' v hv
  rw [hcomb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_baryEval_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_baryEval_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_baryEval_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mapGraph_baryEval_eq

/-- The canonical barycentric homeomorphism using all simplexes, with no purity hypothesis. -/
noncomputable def realizationHomeomorphAll :
    GeometricRealization K.Vertex K.simplexes ≃ₜ K.support := by
  classical
  have hmem : ∀ x : GeometricRealization K.Vertex K.simplexes,
      K.baryEval x.1 ∈ K.support := by
    rintro ⟨x, ⟨h0, h1⟩, t, ht, hsupp⟩
    exact Set.mem_biUnion ht (K.baryEval_mem_cellCarrier hsupp h0 h1)
  let phi : GeometricRealization K.Vertex K.simplexes → K.support :=
    fun x => ⟨K.baryEval x.1, hmem x⟩
  have hcont : Continuous phi :=
    Continuous.subtype_mk (K.continuous_baryEval.comp continuous_subtype_val) _
  have hinj : Function.Injective phi := by
    rintro ⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩ ⟨y, ⟨hy0, hy1⟩, u, hu, hysupp⟩ heq
    have heval : K.baryEval x = K.baryEval y := congrArg Subtype.val heq
    have hpx := K.baryEval_mem_cellCarrier hxsupp hx0 hx1
    have hpy := K.baryEval_mem_cellCarrier hysupp hy0 hy1
    have hpint : K.baryEval x ∈ K.cellCarrier (t ∩ u) := by
      have hfi := K.face_inter t ht u hu
      have hp : K.baryEval x ∈ K.cellCarrier t ∩ K.cellCarrier u :=
        ⟨hpx, by rw [heval]; exact hpy⟩
      change K.baryEval x ∈ convexHull ℝ (K.position '' (t : Set K.Vertex)) ∩
        convexHull ℝ (K.position '' (u : Set K.Vertex)) at hp
      rw [hfi] at hp
      exact hp
    obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hpint
    have hzt : ∀ v ∉ t, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_left hmem)
    have hzu : ∀ v ∉ u, z v = 0 := fun v hv =>
      hzsupp v fun hmem => hv (Finset.mem_of_mem_inter_right hmem)
    have hxz : x = z := K.baryEval_injOn_face ht hxsupp hzt hx1 hz1 (by rw [hzeval])
    have hyz : y = z := K.baryEval_injOn_face hu hysupp hzu hy1 hz1
      (by rw [hzeval, ← heval])
    exact Subtype.ext (hxz.trans hyz.symm)
  have hsurj : Function.Surjective phi := by
    rintro ⟨p, hp⟩
    rw [PlaneComplex.support, Set.mem_iUnion₂] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    obtain ⟨x, hxsupp, hx0, hx1, hxeval⟩ := K.exists_weights_of_mem_cellCarrier hpt
    exact ⟨⟨x, ⟨hx0, hx1⟩, t, ht, hxsupp⟩, Subtype.ext hxeval⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective phi ⟨hinj, hsurj⟩) hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll

@[simp] theorem realizationHomeomorphAll_apply
    (x : GeometricRealization K.Vertex K.simplexes) :
    (K.realizationHomeomorphAll x).1 = K.baryEval x.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll_apply then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll_apply ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.realizationHomeomorphAll_apply

/-- Reposition a plane complex while retaining its abstract simplexes. -/
noncomputable def reposition (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    PlaneComplex where
  Vertex := K.Vertex
  position := position'
  position_injective := hinj
  simplexes := K.simplexes
  nonempty_of_mem := K.nonempty_of_mem
  card_le_three := K.card_le_three
  down_closed := K.down_closed
  affineIndependent := haff
  face_inter := hface

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.reposition then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.reposition"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.reposition ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.reposition

/-- Preserve barycentric coordinates under a repositioning of a complex. -/
noncomputable def repositionHomeomorphAll (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    K.support ≃ₜ (K.reposition position' hinj haff hface).support :=
  K.realizationHomeomorphAll.symm.trans
    (K.reposition position' hinj haff hface).realizationHomeomorphAll

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionHomeomorphAll then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionHomeomorphAll"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionHomeomorphAll ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionHomeomorphAll

/-- The ambient function underlying barycentric repositioning, set to zero off the source
support. -/
noncomputable def repositionMap (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    Plane → Plane := by
  classical
  exact fun x =>
    if hx : x ∈ K.support then
      (K.repositionHomeomorphAll position' hinj haff hface ⟨x, hx⟩).1
    else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap

theorem repositionMap_apply_realization (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    (x : GeometricRealization K.Vertex K.simplexes) :
    K.repositionMap position' hinj haff hface (K.baryEval x.1) =
      (K.reposition position' hinj haff hface).baryEval x.1 := by
  have hxmem : K.baryEval x.1 ∈ K.support :=
    (K.realizationHomeomorphAll x).2
  simp only [repositionMap, dif_pos hxmem, repositionHomeomorphAll]
  change ((K.reposition position' hinj haff hface).realizationHomeomorphAll
    (K.realizationHomeomorphAll.symm ⟨K.baryEval x.1, hxmem⟩)).1 = _
  have heq : K.realizationHomeomorphAll.symm ⟨K.baryEval x.1, hxmem⟩ = x := by
    apply K.realizationHomeomorphAll.injective
    apply Subtype.ext
    simp
  rw [heq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_apply_realization then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_apply_realization"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_apply_realization ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_apply_realization

/-- Barycentric repositioning sends every vertex which occurs as a zero-face to its prescribed
new position. -/
theorem repositionMap_position (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    (v : K.Vertex) (hv : ({v} : Finset K.Vertex) ∈ K.simplexes) :
    K.repositionMap position' hinj haff hface (K.position v) = position' v := by
  classical
  let w : K.Vertex → ℝ := fun u => if u = v then 1 else 0
  have hw0 : ∀ u, 0 ≤ w u := by intro u; simp only [w]; split <;> positivity
  have hw1 : ∑ u, w u = 1 := by simp [w]
  have hwsupp : ∀ u ∉ ({v} : Finset K.Vertex), w u = 0 := by
    intro u hu
    simp only [Finset.mem_singleton] at hu
    simp [w, hu]
  let x : GeometricRealization K.Vertex K.simplexes :=
    ⟨w, ⟨hw0, hw1⟩, {v}, hv, hwsupp⟩
  have hsource : K.baryEval w = K.position v := by
    simp [PlaneComplex.baryEval, w]
  have htarget : (K.reposition position' hinj haff hface).baryEval w = position' v := by
    simp only [PlaneComplex.baryEval, PlaneComplex.reposition, w, ite_smul,
      one_smul, zero_smul]
    exact @Fintype.sum_ite_eq' K.Vertex Plane _
      (K.reposition position' hinj haff hface).vertexFintype K.vertexDecidableEq
      v position'
  rw [← hsource, K.repositionMap_apply_realization position' hinj haff hface x,
    htarget]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_position then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_position"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_position ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_position

/-- Barycentric repositioning is affine on each original face. -/
theorem repositionMap_affineOn_face (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex)))
    {s : Finset K.Vertex} (hs : s ∈ K.simplexes) :
    IsAffineOn (K.repositionMap position' hinj haff hface) (K.cellCarrier s) := by
  classical
  have hsne := K.nonempty_of_mem s hs
  let : Nonempty s := ⟨⟨hsne.choose, hsne.choose_spec⟩⟩
  let p : s → Plane := fun v => K.position v
  let q : s → Plane := fun v => position' v
  obtain ⟨g, hg⟩ := exists_affineMap_eqOn_affineIndependent p q (K.affineIndependent s hs)
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨z, hzsupp, hz0, hz1, hzeval⟩ := K.exists_weights_of_mem_cellCarrier hx
  let xr : GeometricRealization K.Vertex K.simplexes :=
    ⟨z, ⟨hz0, hz1⟩, s, hs, hzsupp⟩
  have hmap : K.repositionMap position' hinj haff hface x =
      (K.reposition position' hinj haff hface).baryEval z := by
    rw [← hzeval]
    exact K.repositionMap_apply_realization position' hinj haff hface xr
  rw [hmap]
  have hsum : ∑ v ∈ s, z v = 1 := by
    rw [← K.sum_eq_sum_of_support hzsupp]
    exact hz1
  have hxcomb : s.affineCombination ℝ K.position z = x := by
    rw [s.affineCombination_eq_linear_combination K.position z hsum]
    exact (K.baryEval_eq_sum_of_support hzsupp).symm.trans hzeval
  rw [← hxcomb, s.map_affineCombination K.position z hsum g]
  have htarget : (K.reposition position' hinj haff hface).baryEval z =
      s.affineCombination ℝ position' z := by
    rw [s.affineCombination_eq_linear_combination position' z hsum]
    change (∑ v, z v • position' v) = ∑ v ∈ s, z v • position' v
    exact (Finset.sum_subset (Finset.subset_univ s)
      (fun v _ hv => by rw [hzsupp v hv, zero_smul])).symm
  rw [htarget]
  change s.affineCombination ℝ position' z =
    s.affineCombination ℝ (g ∘ K.position) z
  apply Finset.affineCombination_congr s (fun _ _ => rfl)
  intro v hv
  exact (hg ⟨v, hv⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_affineOn_face then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_affineOn_face"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_affineOn_face ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_affineOn_face

/-- Barycentric repositioning is PL on the original complex. -/
theorem repositionMap_isPL (position' : K.Vertex → Plane)
    (hinj : Function.Injective position')
    (haff : ∀ s ∈ K.simplexes, AffineIndependent ℝ fun v : s => position' v)
    (hface : ∀ s ∈ K.simplexes, ∀ t ∈ K.simplexes,
      convexHull ℝ (position' '' (s : Set K.Vertex)) ∩
          convexHull ℝ (position' '' (t : Set K.Vertex)) =
        convexHull ℝ (position' '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex))) :
    IsPLOn K (K.repositionMap position' hinj haff hface) := by
  refine ⟨K, PlaneComplex.Subdivides.refl K, ?_⟩
  intro s hs
  exact K.repositionMap_affineOn_face position' hinj haff hface hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_isPL then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_isPL"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_isPL ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.repositionMap_isPL

/-- Vertex positions for the cone on `K`, with `none` as the cone vertex. -/
def conePosition (c : Plane) : Option K.Vertex → Plane
  | none => c
  | some v => K.position v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition

/-- The `coneWeights` declaration. -/
def coneWeights (z : K.Vertex → ℝ) : Option K.Vertex → ℝ
  | none => 0
  | some v => z v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights

@[simp] theorem coneWeights_none (z : K.Vertex → ℝ) : K.coneWeights z _root_.Option.none = 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_none then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_none"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_none ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_none

@[simp] theorem coneWeights_some (z : K.Vertex → ℝ) (v : K.Vertex) :
    K.coneWeights z (_root_.Option.some v) = z v := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_some then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_some"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_some ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneWeights_some

theorem sum_coneWeights (z : K.Vertex → ℝ) :
    ∑ v, K.coneWeights z v = ∑ v, z v := by
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.sum_coneWeights then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.sum_coneWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.sum_coneWeights ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.sum_coneWeights

/-- Lift a base face to the non-cone vertices. -/
def liftFace (s : Finset K.Vertex) : Finset (Option K.Vertex) :=
  s.map Function.Embedding.some

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.liftFace then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.liftFace"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.liftFace ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.liftFace

/-- Remove the cone vertex from a cone face. -/
def baseFace (t : Finset (Option K.Vertex)) : Finset K.Vertex :=
  t.filterMap id (by
    intro a a' b ha ha'
    simpa only [id_eq, Option.mem_def] using ha.trans ha'.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace

@[simp] theorem mem_baseFace {t : Finset (Option K.Vertex)} {v : K.Vertex} :
    v ∈ K.baseFace t ↔ _root_.Option.some v ∈ t := by
  simp [baseFace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_baseFace then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_baseFace"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_baseFace ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_baseFace

@[simp] theorem baseFace_liftFace (s : Finset K.Vertex) :
    K.baseFace (K.liftFace s) = s := by
  ext v
  simp [liftFace]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_liftFace then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_liftFace"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_liftFace ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_liftFace

@[simp] theorem baseFace_inter (t u : Finset (Option K.Vertex)) :
    K.baseFace (t ∩ u) = K.baseFace t ∩ K.baseFace u := by
  ext v
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_inter then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_inter ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_inter

theorem position_image_inter (s t : Finset K.Vertex) :
    K.position '' (s : Set K.Vertex) ∩ K.position '' (t : Set K.Vertex) =
      K.position '' ((s ∩ t : Finset K.Vertex) : Set K.Vertex) := by
  rw [← Set.image_inter K.position_injective, ← Finset.coe_inter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.position_image_inter then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.position_image_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.position_image_inter ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.position_image_inter

theorem conePosition_image_eq_of_not_mem_none {c : Plane}
    {t : Finset (Option K.Vertex)} (ht : _root_.Option.none ∉ t) :
    K.conePosition c '' (t : Set (Option K.Vertex)) =
      K.position '' (K.baseFace t : Set K.Vertex) := by
  ext x
  simp only [Set.mem_image, Finset.mem_coe, mem_baseFace]
  constructor
  · rintro ⟨v, hv, rfl⟩
    cases v with
    | none => exact (ht hv).elim
    | some v => exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨some v, hv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_not_mem_none then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_not_mem_none"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_not_mem_none ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_not_mem_none

theorem conePosition_image_eq_of_mem_none {c : Plane}
    {t : Finset (Option K.Vertex)} (ht : _root_.Option.none ∈ t) :
    K.conePosition c '' (t : Set (Option K.Vertex)) =
      insert c (K.position '' (K.baseFace t : Set K.Vertex)) := by
  ext x
  simp only [Set.mem_image, Finset.mem_coe, mem_baseFace, Set.mem_insert_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    cases v with
    | none => exact Or.inl rfl
    | some v => exact Or.inr ⟨v, hv, rfl⟩
  · rintro (rfl | ⟨v, hv, rfl⟩)
    · exact ⟨none, ht, rfl⟩
    · exact ⟨some v, hv, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_mem_none then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_mem_none"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_mem_none ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_image_eq_of_mem_none

theorem conePosition_injective {c : Plane} (hc : c ∉ Set.range K.position) :
    Function.Injective (K.conePosition c) := by
  intro v w h
  cases v with
  | none =>
      cases w with
      | none => rfl
      | some w =>
          apply (hc ⟨w, ?_⟩).elim
          exact h.symm
  | some v =>
      cases w with
      | none => exact (hc ⟨v, h⟩).elim
      | some w => exact congrArg _root_.Option.some (K.position_injective h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_injective then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_injective ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.conePosition_injective

/-- All nonempty faces of cones on the faces of `K`. -/
def coneSimplexes : Finset (Finset (Option K.Vertex)) :=
  K.simplexes.biUnion fun s =>
    (_root_.Insert.insert _root_.Option.none (K.liftFace s)).powerset.filter (·.Nonempty)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneSimplexes then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneSimplexes"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneSimplexes ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.coneSimplexes

theorem mem_coneSimplexes_iff {t : Finset (Option K.Vertex)} :
    t ∈ K.coneSimplexes ↔
      t.Nonempty ∧ ∃ s ∈ K.simplexes, t ⊆ _root_.Insert.insert _root_.Option.none (K.liftFace s) := by
  simp only [coneSimplexes, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_powerset]
  aesop

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_coneSimplexes_iff then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_coneSimplexes_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_coneSimplexes_iff ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.mem_coneSimplexes_iff

theorem baseFace_subset_of_subset_cone {s : Finset K.Vertex}
    {t : Finset (Option K.Vertex)} (ht : t ⊆ _root_.Insert.insert _root_.Option.none (K.liftFace s)) :
    K.baseFace t ⊆ s := by
  intro v hv
  have hsv := ht (K.mem_baseFace.mp hv)
  simpa [liftFace] using hsv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_subset_of_subset_cone then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_subset_of_subset_cone"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_subset_of_subset_cone ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_subset_of_subset_cone

theorem baseFace_mem_of_nonempty {t : Finset (Option K.Vertex)}
    (ht : t ∈ K.coneSimplexes) (hne : (K.baseFace t).Nonempty) :
    K.baseFace t ∈ K.simplexes := by
  obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
  exact K.down_closed s hs (K.baseFace t) (K.baseFace_subset_of_subset_cone hts) hne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_mem_of_nonempty then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_mem_of_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_mem_of_nonempty ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseFace_mem_of_nonempty

theorem baseCarrier_subset_support {t : Finset (Option K.Vertex)}
    (ht : t ∈ K.coneSimplexes) :
    convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ⊆ K.support := by
  rcases (K.baseFace t).eq_empty_or_nonempty with h | h
  · rw [h]
    simp
  · simpa [PlaneComplex.cellCarrier] using
      K.cellCarrier_subset_support (K.baseFace_mem_of_nonempty ht h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_subset_support then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_subset_support"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_subset_support ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_subset_support

theorem baseCarrier_inter {t u : Finset (Option K.Vertex)}
    (ht : t ∈ K.coneSimplexes) (hu : u ∈ K.coneSimplexes) :
    convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ∩
        convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) =
      convexHull ℝ (K.position '' ((K.baseFace t ∩ K.baseFace u : Finset K.Vertex) :
        Set K.Vertex)) := by
  rcases (K.baseFace t).eq_empty_or_nonempty with h | htne
  · rw [h]
    simp
  rcases (K.baseFace u).eq_empty_or_nonempty with h | hune
  · rw [h]
    simp
  exact K.face_inter _ (K.baseFace_mem_of_nonempty ht htne) _
    (K.baseFace_mem_of_nonempty hu hune)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_inter then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_inter ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.baseCarrier_inter

/-- Cone a finite one-dimensional complex supported on the frontier of a convex set. -/
noncomputable def cone (S : Set Plane) (hS : Convex ℝ S) (c : Plane)
    (hc : c ∈ interior S) (havoid : c ∉ Set.range K.position)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = frontier S) : PlaneComplex where
  Vertex := Option K.Vertex
  position := K.conePosition c
  position_injective := K.conePosition_injective havoid
  simplexes := K.coneSimplexes
  nonempty_of_mem := fun t ht => (K.mem_coneSimplexes_iff.mp ht).1
  card_le_three := by
    intro t ht
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    have hsCard := hgraph s hs
    refine (Finset.card_le_card hts).trans ?_
    calc
      (_root_.Insert.insert _root_.Option.none (K.liftFace s)).card ≤ (K.liftFace s).card + 1 := Finset.card_insert_le _ _
      _ = s.card + 1 := by simp [liftFace]
      _ ≤ 3 := by omega
  down_closed := by
    intro t ht u hut hune
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    exact K.mem_coneSimplexes_iff.mpr ⟨hune, s, hs, hut.trans hts⟩
  affineIndependent := by
    intro t ht
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    let A : Finset Plane := s.image K.position
    have hAI : AffineIndependent ℝ ((↑) : A → Plane) := by
      apply affineIndependent_finset_coe (K.affineIndependent s hs)
      intro a ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha
      exact ⟨⟨v, hv⟩, rfl⟩
    have hAcard : A.card ≤ 2 := by
      rw [Finset.card_image_of_injective _ K.position_injective]
      exact hgraph s hs
    have hAS : convexHull ℝ (A : Set Plane) ⊆ frontier S := by
      rw [← hsupport]
      simpa [A, Finset.coe_image, PlaneComplex.cellCarrier] using
        K.cellCarrier_subset_support hs
    have hparent : AffineIndependent ℝ ((↑) : ↥(_root_.Insert.insert c A) → Plane) :=
      affineIndependent_insert_interior_of_card_le_two hS hAcard hAI hAS hc
    let e : t ↪ ↥(_root_.Insert.insert c A) :=
      { toFun := fun ⟨v, hv⟩ => ⟨K.conePosition c v, by
          cases v with
          | none => exact Finset.mem_insert_self _ _
          | some v =>
              apply Finset.mem_insert_of_mem
              apply Finset.mem_image.mpr
              refine ⟨v, ?_, rfl⟩
              exact K.baseFace_subset_of_subset_cone hts
                (K.mem_baseFace.mpr hv)⟩
        inj' := fun v w h => Subtype.ext
          ((K.conePosition_injective havoid) (congrArg Subtype.val h)) }
    exact hparent.comp_embedding e
  face_inter := by
    intro t ht u hu
    have htBase : convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ⊆
        frontier S := by
      rw [← hsupport]
      exact K.baseCarrier_subset_support ht
    have huBase : convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) ⊆
        frontier S := by
      rw [← hsupport]
      exact K.baseCarrier_subset_support hu
    have hinter := K.baseCarrier_inter ht hu
    have hinterSet :
        convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) ∩
            convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) =
          convexHull ℝ ((K.position '' (K.baseFace t : Set K.Vertex)) ∩
            K.position '' (K.baseFace u : Set K.Vertex)) := by
      rw [K.position_image_inter]
      exact hinter
    by_cases ht0 : _root_.Option.none ∈ t
    · rw [K.conePosition_image_eq_of_mem_none ht0]
      by_cases hu0 : _root_.Option.none ∈ u
      · rw [K.conePosition_image_eq_of_mem_none hu0]
        have htu0 : _root_.Option.none ∈ t ∩ u := Finset.mem_inter.mpr ⟨ht0, hu0⟩
        rw [K.conePosition_image_eq_of_mem_none htu0, K.baseFace_inter]
        simpa [K.position_image_inter] using
          convexHull_insert_inter_convexHull_insert' hS hc htBase huBase hinterSet
      · rw [K.conePosition_image_eq_of_not_mem_none hu0]
        have htu0 : _root_.Option.none ∉ t ∩ u := fun h => hu0 (Finset.mem_inter.mp h).2
        rw [K.conePosition_image_eq_of_not_mem_none htu0, K.baseFace_inter]
        simpa [K.position_image_inter] using
          convexHull_insert_inter_convexHull' hS hc htBase huBase hinterSet
    · rw [K.conePosition_image_eq_of_not_mem_none ht0]
      by_cases hu0 : _root_.Option.none ∈ u
      · rw [K.conePosition_image_eq_of_mem_none hu0]
        have htu0 : _root_.Option.none ∉ t ∩ u := fun h => ht0 (Finset.mem_inter.mp h).1
        rw [K.conePosition_image_eq_of_not_mem_none htu0, K.baseFace_inter]
        have hinterRev :
            convexHull ℝ (K.position '' (K.baseFace u : Set K.Vertex)) ∩
                convexHull ℝ (K.position '' (K.baseFace t : Set K.Vertex)) =
              convexHull ℝ ((K.position '' (K.baseFace u : Set K.Vertex)) ∩
                K.position '' (K.baseFace t : Set K.Vertex)) := by
          rw [K.position_image_inter]
          exact K.baseCarrier_inter hu ht
        have hrev := convexHull_insert_inter_convexHull' hS hc huBase htBase hinterRev
        simpa [Set.inter_comm, Finset.inter_comm, K.position_image_inter] using hrev
      · rw [K.conePosition_image_eq_of_not_mem_none hu0]
        have htu0 : _root_.Option.none ∉ t ∩ u := fun h => ht0 (Finset.mem_inter.mp h).1
        rw [K.conePosition_image_eq_of_not_mem_none htu0, K.baseFace_inter]
        exact hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone

theorem cone_baryEval_coneWeights (S : Set Plane) (hS : Convex ℝ S) (c : Plane)
    (hc : c ∈ interior S) (havoid : c ∉ Set.range K.position)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = frontier S) (z : K.Vertex → ℝ) :
    (K.cone S hS c hc havoid hgraph hsupport).baryEval (K.coneWeights z) =
      K.baryEval z := by
  simp only [PlaneComplex.baryEval, cone]
  change (∑ x : Option K.Vertex, K.coneWeights z x • K.conePosition c x) =
    ∑ v, z v • K.position v
  rw [Fintype.sum_option]
  simp [coneWeights, conePosition]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_baryEval_coneWeights then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_baryEval_coneWeights"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_baryEval_coneWeights ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_baryEval_coneWeights

theorem cone_support_eq (S : Set Plane) (hS : Convex ℝ S) (hcompact : IsCompact S)
    (c : Plane) (hc : c ∈ interior S) (havoid : c ∉ Set.range K.position)
    (hgraph : ∀ s ∈ K.simplexes, s.card ≤ 2)
    (hsupport : K.support = frontier S) (hfrontier : (frontier S).Nonempty) :
    (K.cone S hS c hc havoid hgraph hsupport).support = S := by
  change (⋃ t ∈ K.coneSimplexes,
      convexHull ℝ (K.conePosition c '' (t : Set (Option K.Vertex)))) = S
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    obtain ⟨-, s, hs, hts⟩ := K.mem_coneSimplexes_iff.mp ht
    have hcarrier :
        convexHull ℝ (K.conePosition c '' (t : Set (Option K.Vertex))) ⊆
          convexHull ℝ (_root_.Insert.insert c (K.position '' (s : Set K.Vertex))) := by
      apply convexHull_mono
      rintro z ⟨v, hv, rfl⟩
      have hvParent := hts hv
      cases v with
      | none => exact Set.mem_insert _ _
      | some v =>
          apply Set.mem_insert_of_mem
          refine ⟨v, ?_, rfl⟩
          simpa [liftFace] using hvParent
    apply hcarrier at hxt
    exact (convexHull_min (by
      rintro z (rfl | ⟨v, hv, rfl⟩)
      · exact interior_subset hc
      · have hvCarrier : K.position v ∈ K.cellCarrier s :=
          subset_convexHull ℝ _ ⟨v, hv, rfl⟩
        have hvSupport := K.cellCarrier_subset_support hs hvCarrier
        rw [hsupport] at hvSupport
        exact hcompact.isClosed.frontier_subset hvSupport) hS) hxt
  · intro x hx
    obtain ⟨y, hyFrontier, hxy⟩ :=
      exists_frontier_endpoint hS hcompact hc hx hfrontier
    have hySupport : y ∈ K.support := by simpa [hsupport] using hyFrontier
    rw [PlaneComplex.support] at hySupport
    simp only [Set.mem_iUnion] at hySupport
    obtain ⟨s, hs, hys⟩ := hySupport
    let t : Finset (Option K.Vertex) := _root_.Insert.insert _root_.Option.none (K.liftFace s)
    have ht : t ∈ K.coneSimplexes := by
      apply K.mem_coneSimplexes_iff.mpr
      exact ⟨⟨none, Finset.mem_insert_self _ _⟩, s, hs, subset_rfl⟩
    simp only [Set.mem_iUnion]
    refine ⟨t, ht, ?_⟩
    have ht0 : _root_.Option.none ∈ t := Finset.mem_insert_self _ _
    rw [K.conePosition_image_eq_of_mem_none ht0]
    have hbase : K.baseFace t = s := by
      ext v
      simp [t, liftFace]
    rw [hbase]
    exact (convex_convexHull ℝ (_root_.Insert.insert c (K.position '' (s : Set K.Vertex)))).segment_subset
      (subset_convexHull ℝ _ (Set.mem_insert _ _))
      (convexHull_mono (Set.subset_insert c _) hys) hxy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_support_eq then
    throwError "Refusing to shadow existing declaration LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_support_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_support_eq ``Submission.LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.cone_support_eq

end PlaneComplex

end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
