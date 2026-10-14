/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.FiniteIntervalCuts
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleArcs
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_crossing_subarc_of_finite_boundary_intersection {A T D J : Set E}
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (_root_.Set.Icc 0 1) A) (hAT : A ⊆ T)
    (hD : IsClosed D) (hboundary : D ∩ closure (T \ D) = J) (hfinite : (A ∩ J).Finite)
    (h0 : η 0 ∈ J ∨ η 0 ∉ D) (h1 : η 1 ∈ J ∨ η 1 ∉ D)
    {x : E} (hx : x ∈ A ∩ (D \ J)) :
    ∃ (B : Set E) (γ : ℝ → E), IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) B ∧ B ⊆ A ∩ D ∧
      γ 0 ∈ J ∧ γ 1 ∈ J ∧ B ∩ J = {γ 0, γ 1} ∧
      B \ {γ 0, γ 1} ⊆ D \ J ∧ x ∈ B \ {γ 0, γ 1} := by
  obtain ⟨t, ht, rfl⟩ := hη.bijOn.surjOn hx.1
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact h0.elim hx.2.2 (fun h => h hx.2.1)
  have ht1 : t ≠ 1 := by
    rintro rfl
    exact h1.elim hx.2.2 (fun h => h hx.2.1)
  have ht' : t ∈ _root_.Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 ht0.symm, lt_of_le_of_ne ht.2 ht1⟩
  have hM : (_root_.Set.Icc (0 : ℝ) 1 ∩ η ⁻¹' J).Finite := by
    have himg : η '' (_root_.Set.Icc (0 : ℝ) 1 ∩ η ⁻¹' J) ⊆ A ∩ J := by
      rintro y ⟨s, ⟨hs, hsJ⟩, rfl⟩
      exact ⟨hη.bijOn.mapsTo hs, hsJ⟩
    exact (hfinite.subset himg).of_finite_image (hη.bijOn.injOn.mono _root_.Set.inter_subset_left)
  obtain ⟨a, b, ha0, hat, htb, hb1, haJ, hbJ, hinside⟩ :=
    exists_subinterval_of_finite_boundary_preimage hη.isPiecewiseAffineOn.continuousOn
      (fun s hs => hAT (hη.bijOn.mapsTo hs)) hD hboundary hM h0 h1 ht' hx.2
  have hab : a < b := hat.trans htb
  have hsub : _root_.Set.Icc a b ⊆ _root_.Set.Icc (0 : ℝ) 1 := fun s hs => ⟨ha0.trans hs.1, hs.2.trans hb1⟩
  let B := η '' _root_.Set.Icc a b
  have hηab : IsPLHomeomorphOn η (_root_.Set.Icc a b) B :=
    hη.restrict (isPLBall_Icc hab).isPolyhedron hsub
  have hBA : B ⊆ A := (_root_.Set.image_mono hsub).trans hη.image_eq.subset
  have hopen : B \ {η a, η b} ⊆ D \ J := by
    rw [← hηab.image_Ioo_eq_sdiff_endpoints hab]
    exact image_subset_iff.mpr hinside
  have hBD : B ⊆ D := by
    rw [← hηab.closure_sdiff_endpoints hab]
    exact closure_minimal (hopen.trans _root_.Set.sdiff_subset) hD
  obtain ⟨φ, hφ, hφ0, hφ1⟩ := exists_isPLHomeomorphOn_Icc_map_endpoints
    (by norm_num : (0 : ℝ) < 1) hab
  have hγ : IsPLHomeomorphOn (η ∘ φ) (_root_.Set.Icc 0 1) B := hφ.trans hηab
  have hγ0 : (η ∘ φ) 0 = η a := congrArg η hφ0
  have hγ1 : (η ∘ φ) 1 = η b := congrArg η hφ1
  have hBJ : B ∩ J = {η a, η b} := by
    apply Subset.antisymm
    · rintro y ⟨hyB, hyJ⟩
      by_contra hy
      exact (hopen ⟨hyB, hy⟩).2 hyJ
    · intro y hy
      exact ⟨(_root_.Set.pair_subset (hηab.bijOn.mapsTo ⟨le_rfl, hab.le⟩)
        (hηab.bijOn.mapsTo ⟨hab.le, le_rfl⟩)) hy, (_root_.Set.pair_subset haJ hbJ) hy⟩
  refine ⟨B, η ∘ φ, hγ, _root_.Set.subset_inter hBA hBD, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [hγ0]
  · rwa [hγ1]
  · rwa [hγ0, hγ1]
  · simpa only [hγ0, hγ1] using hopen
  · rw [hγ0, hγ1, ← hηab.image_Ioo_eq_sdiff_endpoints hab]
    exact ⟨t, ⟨hat, htb⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_crossing_subarc_of_finite_boundary_intersection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_crossing_subarc_of_finite_boundary_intersection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_crossing_subarc_of_finite_boundary_intersection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_crossing_subarc_of_finite_boundary_intersection

end DifferentialGeometry.Topology.PiecewiseLinear
