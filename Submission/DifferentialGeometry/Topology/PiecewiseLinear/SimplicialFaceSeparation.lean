/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Barycentric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem disjoint_openSimplex_convexHull_of_not_subset
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : ¬s ⊆ t) :
    Disjoint (openSimplex s) (convexHull ℝ (t : Set E)) :=
  disjoint_left.mpr fun _ hxs hxt =>
    hst (face_subset_of_mem_openSimplex_of_mem_convexHull K hs ht hxs hxt)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_not_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_not_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_not_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_not_subset

theorem convexHull_subset_or_disjoint_openSimplex
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) ∨
      Disjoint (openSimplex s) (convexHull ℝ (t : Set E)) := by
  by_cases hst : s ⊆ t
  · exact Or.inl (convexHull_mono hst)
  · exact Or.inr (disjoint_openSimplex_convexHull_of_not_subset K hs ht hst)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.convexHull_subset_or_disjoint_openSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.convexHull_subset_or_disjoint_openSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.convexHull_subset_or_disjoint_openSimplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.convexHull_subset_or_disjoint_openSimplex

theorem disjoint_openSimplex_convexHull_of_card_eq
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hcard : s.card = t.card) (hne : s ≠ t) :
    Disjoint (openSimplex s) (convexHull ℝ (t : Set E)) :=
  disjoint_openSimplex_convexHull_of_not_subset K hs ht
    (fun hst => hne (Finset.eq_of_subset_of_card_le hst hcard.ge))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_card_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_card_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_card_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_convexHull_of_card_eq

theorem disjoint_openSimplex_vertices_of_one_lt_card
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}
    (hs : s ∈ K.faces) (hcard : 1 < s.card) : Disjoint (openSimplex s) K.vertices := by
  apply disjoint_left.mpr
  intro x hxs hxv
  have hx : x ∈ convexHull ℝ (({x} : Finset E) : Set E) :=
    subset_convexHull ℝ _ (by simp)
  have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull K hs hxv hxs hx
  have h := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at h
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_vertices_of_one_lt_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_vertices_of_one_lt_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_vertices_of_one_lt_card ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.disjoint_openSimplex_vertices_of_one_lt_card

theorem openSimplex_pair_eq_openSegment [DecidableEq E] {p q : E} (hpq : p ≠ q) :
    openSimplex ({p, q} : Finset E) = openSegment ℝ p q := by
  ext x
  constructor
  · rintro ⟨w, hw, hsum, hx⟩
    rw [Finset.sum_pair hpq] at hsum hx
    exact ⟨w p, w q, hw p (by simp), hw q (by simp), hsum, hx⟩
  · rintro ⟨a, b, ha, hb, hab, hx⟩
    refine ⟨fun y => if y = p then a else b, ?_, ?_, ?_⟩
    · intro y hy
      rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy :
        y = p ∨ y = q) with rfl | rfl
      · simpa using ha
      · simpa only [if_neg hpq.symm] using hb
    · simpa [Finset.sum_pair hpq, hpq.symm] using hab
    · simpa [Finset.sum_pair hpq, hpq.symm] using hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.openSimplex_pair_eq_openSegment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.openSimplex_pair_eq_openSegment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.openSimplex_pair_eq_openSegment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.openSimplex_pair_eq_openSegment

end DifferentialGeometry.Topology.PiecewiseLinear
