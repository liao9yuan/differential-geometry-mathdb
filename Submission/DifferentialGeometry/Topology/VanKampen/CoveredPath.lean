/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Submission.DifferentialGeometry.Topology.VanKampen.Subdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Metric _root_.Set _root_.unitInterval
open scoped _root_.unitInterval

universe u

namespace DifferentialGeometry.Topology.VanKampen

namespace Path

def IsCovered {X : Type u} [TopologicalSpace X] {a b : X} (p : _root_.Path a b)
    (U V : Set X) (n : ℕ) : Prop :=
  ∀ i : Fin n, _root_.Set.range (standardSubpath p i) ⊆ U ∨ _root_.Set.range (standardSubpath p i) ⊆ V

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.Path.IsCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.Path.IsCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.Path.IsCovered ``Submission.DifferentialGeometry.Topology.VanKampen.Path.IsCovered

theorem dist_standardTime_le {n : ℕ} (hn : 0 < n) (i : Fin n) (t : I)
    (ht : t ∈ _root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ)) :
    dist (standardTime n i.castSucc) t ≤ 1 / (n : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos, neg_sub]
  · calc
      (t : ℝ) - standardTime n i.castSucc ≤
          standardTime n i.succ - standardTime n i.castSucc := by
        exact sub_le_sub_right (by exact_mod_cast ht.2) _
      _ = 1 / (n : ℝ) := standardTime_succ_sub_castSucc hn i
  · exact sub_nonpos.mpr (by exact_mod_cast ht.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.Path.dist_standardTime_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.Path.dist_standardTime_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.Path.dist_standardTime_le ``Submission.DifferentialGeometry.Topology.VanKampen.Path.dist_standardTime_le

theorem exists_isCovered {X : Type u} [TopologicalSpace X] {a b : X} (p : _root_.Path a b)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = _root_.Set.univ) :
    ∃ n : ℕ, 0 < n ∧ IsCovered p U V n := by
  let c : Bool → Set I := fun side ↦ p ⁻¹' if side then U else V
  have hc_open : ∀ side, IsOpen (c side) := by
    intro side
    cases side <;> simp [c, hU, hV, p.continuous.isOpen_preimage]
  have hc_cover : (_root_.Set.univ : Set I) ⊆ ⋃ side, c side := by
    intro t _
    have ht : p t ∈ U ∪ V := by rw [hcover]; trivial
    rcases ht with htU | htV
    · exact mem_iUnion.mpr ⟨true, by simpa [c] using htU⟩
    · exact mem_iUnion.mpr ⟨false, by simpa [c] using htV⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric (s := (_root_.Set.univ : Set I)) isCompact_univ hc_open hc_cover
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (K := ℝ) hδ
  let n := m + 1
  have hn : 0 < n := Nat.succ_pos m
  have hmesh : 1 / (n : ℝ) < δ := by simpa [n] using hm
  refine ⟨n, hn, ?_⟩
  intro i
  obtain ⟨side, hside⟩ := hball (standardTime n i.castSucc) (_root_.Set.mem_univ _)
  have hinterval : _root_.Set.Icc (standardTime n i.castSucc) (standardTime n i.succ) ⊆ c side := by
    intro t ht
    apply hside
    rw [_root_.Metric.mem_ball]
    simpa [dist_comm] using (dist_standardTime_le hn i t ht).trans_lt hmesh
  have hrange : _root_.Set.range (standardSubpath p i) ⊆ if side then U else V := by
    rw [standardSubpath, _root_.Path.range_subpath_of_le _ _ _
      (standardTime_castSucc_le_succ hn i)]
    rintro _ ⟨t, ht, rfl⟩
    exact hinterval ht
  cases side
  · exact Or.inr hrange
  · exact Or.inl hrange

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.Path.exists_isCovered then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.Path.exists_isCovered"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.Path.exists_isCovered ``Submission.DifferentialGeometry.Topology.VanKampen.Path.exists_isCovered

theorem IsCovered.mul {X : Type u} [TopologicalSpace X] {a b : X} {p : _root_.Path a b}
    {U V : Set X} {n k : ℕ} (h : IsCovered p U V n) (hn : 0 < n) (hk : 0 < k) :
    IsCovered p U V (n * k) := by
  intro j
  let i : Fin n := ⟨j / k, (Nat.div_lt_iff_lt_mul hk).mpr j.isLt⟩
  let r : Fin k := ⟨j % k, Nat.mod_lt j hk⟩
  have hj : refinedIndex i r = j := by
    apply Fin.ext
    simpa [refinedIndex, i, r, Nat.mul_comm] using Nat.div_add_mod j k
  rw [← hj]
  rcases h i with hiU | hiV
  · exact Or.inl ((range_standardSubpath_refined_subset p hn hk i r).trans hiU)
  · exact Or.inr ((range_standardSubpath_refined_subset p hn hk i r).trans hiV)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.VanKampen.Path.IsCovered
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.Path.IsCovered.mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.Path.IsCovered.mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.Path.IsCovered.mul ``Submission.DifferentialGeometry.Topology.VanKampen.Path.IsCovered.mul

end Path

end DifferentialGeometry.Topology.VanKampen
