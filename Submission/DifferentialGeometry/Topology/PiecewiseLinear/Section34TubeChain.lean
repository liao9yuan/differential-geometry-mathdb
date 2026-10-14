/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeCrossing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric _root_.Submission.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isCompact_segment_euclidean (a b : E3) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isCompact_segment_euclidean then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isCompact_segment_euclidean"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isCompact_segment_euclidean ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isCompact_segment_euclidean

theorem exists_isPLBall_union_prismChain (k : ℕ) :
    ∀ {Y O : Set E3} {u ν : ℕ → E3} {ρ : ℝ}, IsPLBall 3 Y → 0 < ρ →
      Y ∩ _root_.Metric.ball (u 0) ρ = {x | _root_.Inner.inner ℝ (ν 0) (x - u 0) ≤ 0} ∩ _root_.Metric.ball (u 0) ρ → IsOpen O →
      (∀ j < k, segment ℝ (u j) (u (j + 1)) ⊆ O) →
      (∀ j ≤ k, 0 < _root_.Inner.inner ℝ (ν j) (u (j + 1) - u j)) →
      (∀ j < k, 0 < _root_.Inner.inner ℝ (ν (j + 1)) (u (j + 1) - u j)) →
      (∀ j ≤ k, ∀ x ∈ segment ℝ (u j) (u (j + 1)), x ∈ Y → x = u 0) →
      (∀ i j, j ≤ k → i + 1 < j →
        Disjoint (segment ℝ (u i) (u (i + 1))) (segment ℝ (u j) (u (j + 1)))) →
      (∀ j < k, segment ℝ (u j) (u (j + 1)) ∩ segment ℝ (u (j + 1)) (u (j + 2)) ⊆
        {u (j + 1)}) →
      ∃ N : Set E3, IsCompact N ∧ N ⊆ O ∧ IsPLBall 3 (Y ∪ N) ∧
        (∃ ρ' > 0, (Y ∪ N) ∩ _root_.Metric.ball (u k) ρ' =
          {x | _root_.Inner.inner ℝ (ν k) (x - u k) ≤ 0} ∩ _root_.Metric.ball (u k) ρ') ∧
        ∀ x ∈ segment ℝ (u k) (u (k + 1)), x ∈ Y ∪ N → x = u k := by
  induction k with
  | zero =>
    intro Y O u ν ρ hY hρ hflat _ _ _ _ hYA _ _
    refine ⟨∅, isCompact_empty, _root_.Set.empty_subset _, by rwa [_root_.Set.union_empty], ⟨ρ, hρ, by
      rwa [_root_.Set.union_empty]⟩, fun x hx hxY => hYA 0 le_rfl x hx ?_⟩
    rwa [_root_.Set.union_empty] at hxY
  | succ k ih =>
    intro Y O u ν ρ hY hρ hflat hO hsegO hν hν' hYA hdisj hadj
    set A := ⋃ j ∈ Finset.Icc 2 (k + 1), segment ℝ (u j) (u (j + 1)) with hA
    have hAc : IsClosed A :=
      (Finset.Icc 2 (k + 1)).finite_toSet.isClosed_biUnion fun j _ =>
        (isCompact_segment_euclidean _ _).isClosed
    have hseg0A : Disjoint (segment ℝ (u 0) (u 1)) A := by
      refine Set.disjoint_left.mpr fun x hx hxA => ?_
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxA
      rw [Finset.mem_Icc] at hj
      exact Set.disjoint_left.mp (hdisj 0 j hj.2 (by omega)) hx hxj
    have hu01 : u 1 ≠ u 0 := by
      intro h
      have := hν 0 (Nat.zero_le _)
      rw [zero_add, h, sub_self, inner_zero_right] at this
      exact lt_irrefl _ this
    have hsegY : ∀ x ∈ segment ℝ (u 0) (u 1), x ≠ u 0 → x ∉ Y := fun x hx hne hxY =>
      hne (hYA 0 (Nat.zero_le _) x hx hxY)
    have hV : IsOpen (O ∩ Aᶜ) := hO.inter hAc.isOpen_compl
    have hsegV : segment ℝ (u 0) (u 1) ⊆ O ∩ Aᶜ := fun x hx =>
      ⟨hsegO 0 (Nat.succ_pos _) hx, Set.disjoint_left.mp hseg0A hx⟩
    obtain ⟨C, hCpoly, hCV, hCtop, -, hQ, ⟨ρ', hρ', hflat'⟩, -⟩ :=
      exists_isPLBall_union_prism hY hρ hflat (hν 0 (Nat.zero_le _))
        (hν' 0 (Nat.succ_pos _)) hsegY hV hsegV
    have hν1 : 0 < _root_.Inner.inner ℝ (ν 1) (u 2 - u 1) := hν 1 (by omega)
    have hYA' : ∀ j ≤ k, ∀ x ∈ segment ℝ (u (j + 1)) (u (j + 1 + 1)), x ∈ Y ∪ C → x = u 1 := by
      intro j hj x hx hxYC
      change x ∈ segment ℝ (u (j + 1)) (u (j + 1 + 1)) at hx
      rcases hxYC with hxY | hxC
      · exfalso
        have hx0 := hYA (j + 1) (by omega) x hx hxY
        rw [hx0] at hx
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          have h01 := hadj 0 (Nat.succ_pos _) ⟨left_mem_segment ℝ _ _, hx⟩
          exact hu01 (mem_singleton_iff.mp h01).symm
        · exact Set.disjoint_left.mp (hdisj 0 (j + 1) (by omega) (by omega))
            (left_mem_segment ℝ _ _) hx
      · rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          change x ∈ segment ℝ (u 1) (u 2) at hx
          rw [segment_eq_image'] at hx
          obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hx
          have hle : _root_.Inner.inner ℝ (ν 1) (u 1 + t • (u 2 - u 1) - u 1) ≤ 0 := hCtop hxC
          rw [add_sub_cancel_left, real_inner_smul_right] at hle
          have ht : t = 0 := le_antisymm (by nlinarith) ht0
          change u 1 + t • (u 2 - u 1) = u (0 + 1)
          rw [ht, zero_smul, add_zero]
        · exfalso
          have hxA : x ∈ A :=
            mem_iUnion₂.mpr ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hx⟩
          exact (hCV hxC).2 hxA
    obtain ⟨N', hN'c, hN'O, hN'ball, hN'flat, hN'seg⟩ :=
      ih (Y := Y ∪ C) (O := O) (u := fun j => u (j + 1)) (ν := fun j => ν (j + 1)) hQ hρ'
        hflat' hO (fun j hj => hsegO (j + 1) (by omega)) (fun j hj => hν (j + 1) (by omega))
        (fun j hj => hν' (j + 1) (by omega)) hYA'
        (fun i j hj hij => hdisj (i + 1) (j + 1) (by omega) (by omega))
        (fun j hj => hadj (j + 1) (by omega))
    refine ⟨C ∪ N', hCpoly.isCompact.union hN'c, _root_.Set.union_subset (fun x hx => (hCV hx).1) hN'O,
      by rwa [← _root_.Set.union_assoc], ?_, ?_⟩
    · rwa [← _root_.Set.union_assoc]
    · intro x hx hxN
      rw [← _root_.Set.union_assoc] at hxN
      exact hN'seg x hx hxN

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_union_prismChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_union_prismChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_union_prismChain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLBall_union_prismChain

theorem isPLBall_sdiff_interior_union_prismChain {X W O : Set E3} {u ν : ℕ → E3} {m : ℕ}
    {b nb : E3} {ρ ρb : ℝ} (hX : IsPLBall 3 X) (hW : IsPLBall 3 W) (hXW : X ⊆ interior W)
    (hO : IsOpen O) (hρ : 0 < ρ)
    (hflatX : X ∩ _root_.Metric.ball (u 0) ρ = {x | _root_.Inner.inner ℝ (ν 0) (x - u 0) ≤ 0} ∩ _root_.Metric.ball (u 0) ρ)
    (hρb : 0 < ρb) (hflatW : W ∩ _root_.Metric.ball b ρb = {x | _root_.Inner.inner ℝ nb (x - b) ≤ 0} ∩ _root_.Metric.ball b ρb)
    (hsegO : ∀ j ≤ m, segment ℝ (u j) (u (j + 1)) ⊆ O)
    (hsegW' : ∀ j < m, segment ℝ (u j) (u (j + 1)) ⊆ interior W)
    (hb : b ∈ openSegment ℝ (u m) (u (m + 1)))
    (hsegW : ∀ x ∈ segment ℝ (u m) (u (m + 1)), x ∈ frontier W → x = b)
    (hν : ∀ j ≤ m, 0 < _root_.Inner.inner ℝ (ν j) (u (j + 1) - u j))
    (hν' : ∀ j < m, 0 < _root_.Inner.inner ℝ (ν (j + 1)) (u (j + 1) - u j))
    (hnb : 0 < _root_.Inner.inner ℝ nb (u (m + 1) - u m))
    (hXA : ∀ j ≤ m, ∀ x ∈ segment ℝ (u j) (u (j + 1)), x ∈ X → x = u 0)
    (hdisj : ∀ i j, j ≤ m → i + 1 < j →
      Disjoint (segment ℝ (u i) (u (i + 1))) (segment ℝ (u j) (u (j + 1))))
    (hadj : ∀ j < m, segment ℝ (u j) (u (j + 1)) ∩ segment ℝ (u (j + 1)) (u (j + 2)) ⊆
      {u (j + 1)}) :
    ∃ N : Set E3, IsCompact N ∧ N ⊆ O ∧ IsPLBall 3 (W \ interior (X ∪ N)) := by
  obtain ⟨N, hNc, hNO, hNball, ⟨ρ', hρ', hflat'⟩, hNseg⟩ :=
    exists_isPLBall_union_prismChain m hX hρ hflatX (hO.inter isOpen_interior)
      (fun j hj x hx => ⟨hsegO j hj.le hx, hsegW' j hj hx⟩) hν hν' hXA hdisj hadj
  have hYW : X ∪ N ⊆ interior W := _root_.Set.union_subset hXW fun x hx => (hNO hx).2
  obtain ⟨C, hCc, hCO, hball⟩ := isPLBall_sdiff_interior_union_prism hW hNball hYW hρ' hflat'
    hρb hflatW hb (hν m le_rfl) hnb (fun x hx hne hxY => hne (hNseg x hx hxY)) hsegW hO
    (hsegO m le_rfl)
  refine ⟨N ∪ C, hNc.union hCc, _root_.Set.union_subset (fun x hx => (hNO hx).1) hCO, ?_⟩
  rwa [← _root_.Set.union_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_sdiff_interior_union_prismChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_sdiff_interior_union_prismChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_sdiff_interior_union_prismChain ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_sdiff_interior_union_prismChain

end DifferentialGeometry.Topology.PiecewiseLinear
