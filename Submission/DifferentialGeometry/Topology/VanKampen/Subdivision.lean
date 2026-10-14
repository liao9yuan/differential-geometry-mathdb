/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Topology.Subpath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.unitInterval
open scoped _root_.unitInterval

universe u

namespace DifferentialGeometry.Topology.VanKampen

noncomputable def standardTime (n : ℕ) (i : Fin (n + 1)) : I :=
  ⟨(i : ℝ) / (n : ℝ), unitInterval.div_mem (by positivity) (by positivity) (by
    exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardTime ``Submission.DifferentialGeometry.Topology.VanKampen.standardTime

@[simp]
theorem standardTime_zero (n : ℕ) : standardTime n 0 = 0 := by
  ext
  simp [standardTime]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardTime_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardTime_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardTime_zero ``Submission.DifferentialGeometry.Topology.VanKampen.standardTime_zero

@[simp]
theorem standardTime_last {n : ℕ} (hn : 0 < n) : standardTime n (Fin.last n) = 1 := by
  ext
  simp [standardTime, Nat.ne_of_gt hn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardTime_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardTime_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardTime_last ``Submission.DifferentialGeometry.Topology.VanKampen.standardTime_last

theorem standardTime_castSucc_le_succ {n : ℕ} (hn : 0 < n) (i : Fin n) :
    standardTime n i.castSucc ≤ standardTime n i.succ := by
  rw [← Subtype.coe_le_coe]
  simp only [standardTime, Subtype.coe_mk]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (by positivity)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardTime_castSucc_le_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardTime_castSucc_le_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardTime_castSucc_le_succ ``Submission.DifferentialGeometry.Topology.VanKampen.standardTime_castSucc_le_succ

theorem standardTime_succ_sub_castSucc {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (standardTime n i.succ : ℝ) - standardTime n i.castSucc = 1 / (n : ℝ) := by
  simp only [standardTime, Subtype.coe_mk, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
    Nat.cast_one]
  field_simp [Nat.ne_of_gt hn]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardTime_succ_sub_castSucc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardTime_succ_sub_castSucc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardTime_succ_sub_castSucc ``Submission.DifferentialGeometry.Topology.VanKampen.standardTime_succ_sub_castSucc

noncomputable def standardSubpath {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n : ℕ} (i : Fin n) :
    Path (p (standardTime n i.castSucc)) (p (standardTime n i.succ)) :=
  p.subpath (standardTime n i.castSucc) (standardTime n i.succ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardSubpath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardSubpath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardSubpath ``Submission.DifferentialGeometry.Topology.VanKampen.standardSubpath

def refinedIndex {n k : ℕ} (i : Fin n) (r : Fin k) : Fin (n * k) :=
  ⟨i * k + r, (Nat.add_lt_add_left r.isLt (i * k)).trans_le (by
    simpa [Nat.succ_mul] using Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr i.isLt))⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.refinedIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.refinedIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.refinedIndex ``Submission.DifferentialGeometry.Topology.VanKampen.refinedIndex

@[simp]
theorem refinedIndex_val {n k : ℕ} (i : Fin n) (r : Fin k) :
    (refinedIndex i r : ℕ) = i * k + r :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.refinedIndex_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.refinedIndex_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.refinedIndex_val ``Submission.DifferentialGeometry.Topology.VanKampen.refinedIndex_val

def refinedVertex {n k : ℕ} (i : Fin n) (r : Fin (k + 1)) : Fin (n * k + 1) :=
  ⟨i * k + r, by
    apply Nat.lt_succ_of_le
    calc
      i * k + r ≤ i * k + k := Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) _
      _ = (i + 1) * k := by rw [Nat.add_mul, one_mul]
      _ ≤ n * k := Nat.mul_le_mul_right k (Nat.succ_le_iff.mpr i.isLt)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.refinedVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.refinedVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.refinedVertex ``Submission.DifferentialGeometry.Topology.VanKampen.refinedVertex

@[simp]
theorem refinedVertex_val {n k : ℕ} (i : Fin n) (r : Fin (k + 1)) :
    (refinedVertex i r : ℕ) = i * k + r :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.refinedVertex_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.refinedVertex_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.refinedVertex_val ``Submission.DifferentialGeometry.Topology.VanKampen.refinedVertex_val

theorem standardSubpath_refinedVertex {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (i : Fin n) (r : Fin (k + 1)) :
    standardSubpath p i (standardTime k r) =
      p (standardTime (n * k) (refinedVertex i r)) := by
  apply congrArg p
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb, standardTime, refinedVertex_val, Fin.val_castSucc,
    Fin.val_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  field_simp [Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardSubpath_refinedVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardSubpath_refinedVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardSubpath_refinedVertex ``Submission.DifferentialGeometry.Topology.VanKampen.standardSubpath_refinedVertex

def firstHalfIndex {n : ℕ} (_hn : 0 < n) (i : Fin n) : Fin (2 * n) :=
  ⟨i, by omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.firstHalfIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.firstHalfIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.firstHalfIndex ``Submission.DifferentialGeometry.Topology.VanKampen.firstHalfIndex

def secondHalfIndex {n : ℕ} (_hn : 0 < n) (i : Fin n) : Fin (2 * n) :=
  ⟨n + i, by omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.secondHalfIndex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.secondHalfIndex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.secondHalfIndex ``Submission.DifferentialGeometry.Topology.VanKampen.secondHalfIndex

def firstHalfVertex {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨i, by omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.firstHalfVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.firstHalfVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.firstHalfVertex ``Submission.DifferentialGeometry.Topology.VanKampen.firstHalfVertex

def secondHalfVertex {n : ℕ} (i : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨n + i, by omega⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.secondHalfVertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.secondHalfVertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.secondHalfVertex ``Submission.DifferentialGeometry.Topology.VanKampen.secondHalfVertex

theorem trans_standardTime_first {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin (n + 1)) :
    (p.trans q) (standardTime (2 * n) (firstHalfVertex hn i)) =
      p (standardTime n i) := by
  let t := standardTime (2 * n) (firstHalfVertex hn i)
  have ht : (t : ℝ) ≤ 1 / 2 := by
    dsimp only [t]
    simp only [standardTime, firstHalfVertex, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    have hi : (i : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_lt_succ i.isLt
    linarith
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_le_half p q ht]
  have harg : 2 * (t : ℝ) = (standardTime n i : ℝ) := by
    dsimp only [t]
    simp only [standardTime, firstHalfVertex, Nat.cast_mul, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
  rw [harg, Path.extend_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.trans_standardTime_first then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.trans_standardTime_first"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.trans_standardTime_first ``Submission.DifferentialGeometry.Topology.VanKampen.trans_standardTime_first

theorem trans_standardTime_second {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin (n + 1)) :
    (p.trans q) (standardTime (2 * n) (secondHalfVertex i)) =
      q (standardTime n i) := by
  let t := standardTime (2 * n) (secondHalfVertex i)
  have ht : 1 / 2 ≤ (t : ℝ) := by
    dsimp only [t]
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    simp only [standardTime, secondHalfVertex, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    linarith
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_half_le p q ht]
  have harg : 2 * (t : ℝ) - 1 = (standardTime n i : ℝ) := by
    dsimp only [t]
    simp only [standardTime, secondHalfVertex, Nat.cast_mul, Nat.cast_add,
      Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    ring
  rw [harg, Path.extend_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.trans_standardTime_second then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.trans_standardTime_second"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.trans_standardTime_second ``Submission.DifferentialGeometry.Topology.VanKampen.trans_standardTime_second

theorem standardSubpath_trans_first_apply {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin n) (s : I) :
    standardSubpath (p.trans q) (firstHalfIndex hn i) s = standardSubpath p i s := by
  let t := Set.Icc.convexComb
    (standardTime (2 * n) (firstHalfIndex hn i).castSucc)
    (standardTime (2 * n) (firstHalfIndex hn i).succ) s
  have ht : (t : ℝ) ≤ 1 / 2 := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    simp only [standardTime, firstHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    have hi : (i : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_iff.mpr i.isLt
    ring_nf
    nlinarith
  change (p.trans q) t = p (Set.Icc.convexComb
    (standardTime n i.castSucc) (standardTime n i.succ) s)
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_le_half p q ht]
  have harg : 2 * (t : ℝ) =
      (Set.Icc.convexComb (standardTime n i.castSucc)
        (standardTime n i.succ) s : ℝ) := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb, Set.Icc.coe_convexComb]
    simp only [standardTime, firstHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
  rw [harg, Path.extend_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_first_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_first_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_first_apply ``Submission.DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_first_apply

theorem standardSubpath_trans_second_apply {X : Type u} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) {n : ℕ} (hn : 0 < n)
    (i : Fin n) (s : I) :
    standardSubpath (p.trans q) (secondHalfIndex hn i) s = standardSubpath q i s := by
  let t := Set.Icc.convexComb
    (standardTime (2 * n) (secondHalfIndex hn i).castSucc)
    (standardTime (2 * n) (secondHalfIndex hn i).succ) s
  have ht : 1 / 2 ≤ (t : ℝ) := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb]
    have hs0 : 0 ≤ (s : ℝ) := s.2.1
    have hs1 : (s : ℝ) ≤ 1 := s.2.2
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    simp only [standardTime, secondHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    ring_nf
    nlinarith
  change (p.trans q) t = q (Set.Icc.convexComb
    (standardTime n i.castSucc) (standardTime n i.succ) s)
  rw [← Path.extend_apply (p.trans q) t.property,
    Path.extend_trans_of_half_le p q ht]
  have harg : 2 * (t : ℝ) - 1 =
      (Set.Icc.convexComb (standardTime n i.castSucc)
        (standardTime n i.succ) s : ℝ) := by
    dsimp only [t]
    rw [Set.Icc.coe_convexComb, Set.Icc.coe_convexComb]
    simp only [standardTime, secondHalfIndex, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [Nat.ne_of_gt hn]
    ring
  rw [harg, Path.extend_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_second_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_second_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_second_apply ``Submission.DifferentialGeometry.Topology.VanKampen.standardSubpath_trans_second_apply

theorem standardSubpath_refined_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : Fin n) (r : Fin k) (s : I) :
    standardSubpath p (refinedIndex i r) s = standardSubpath (standardSubpath p i) r s := by
  change p (Set.Icc.convexComb
      (standardTime (n * k) (refinedIndex i r).castSucc)
      (standardTime (n * k) (refinedIndex i r).succ) s) =
    p (Set.Icc.convexComb (standardTime n i.castSucc) (standardTime n i.succ)
      (Set.Icc.convexComb (standardTime k r.castSucc) (standardTime k r.succ) s))
  apply congrArg p
  apply Subtype.ext
  simp only [standardTime, Set.Icc.coe_convexComb, refinedIndex_val, Fin.val_castSucc,
    Fin.val_succ, Nat.cast_add, Nat.cast_mul]
  field_simp [Nat.ne_of_gt hn, Nat.ne_of_gt hk]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardSubpath_refined_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardSubpath_refined_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardSubpath_refined_apply ``Submission.DifferentialGeometry.Topology.VanKampen.standardSubpath_refined_apply

theorem range_standardSubpath_refined_subset {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (i : Fin n) (r : Fin k) :
    Set.range (standardSubpath p (refinedIndex i r)) ⊆ Set.range (standardSubpath p i) := by
  rintro _ ⟨s, rfl⟩
  refine ⟨Set.Icc.convexComb (standardTime k r.castSucc) (standardTime k r.succ) s, ?_⟩
  exact (standardSubpath_refined_apply p hn hk i r s).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.range_standardSubpath_refined_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.range_standardSubpath_refined_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.range_standardSubpath_refined_subset ``Submission.DifferentialGeometry.Topology.VanKampen.range_standardSubpath_refined_subset

noncomputable def standardConcat {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n : ℕ} (hn : 0 < n) : Path a b :=
  (Path.concat (p ∘ standardTime n) (standardSubpath p)).cast
    (by simp) (by simp [standardTime_last hn])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardConcat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardConcat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardConcat ``Submission.DifferentialGeometry.Topology.VanKampen.standardConcat

theorem standardConcat_quotient_eq {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n : ℕ} (hn : 0 < n) :
    Path.Homotopic.Quotient.mk (standardConcat p hn) = Path.Homotopic.Quotient.mk p := by
  rw [Path.Homotopic.Quotient.eq]
  let hx : a = p (standardTime n 0) := by simp
  let hy : b = p (standardTime n (Fin.last n)) := by simp [standardTime_last hn]
  have h := Path.Homotopic.concat_subpath p (standardTime n)
  have hcast :
      ((Path.concat (p ∘ standardTime n) (standardSubpath p)).cast hx hy).Homotopic
        ((p.subpath (standardTime n 0) (standardTime n (Fin.last n))).cast hx hy) :=
    h.pathCast hx hy
  have hright :
      (p.subpath (standardTime n 0) (standardTime n (Fin.last n))).cast hx hy = p := by
    ext s
    simp [Path.subpath, standardTime_last hn]
  rw [hright] at hcast
  simpa only [standardConcat] using hcast

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardConcat_quotient_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardConcat_quotient_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardConcat_quotient_eq ``Submission.DifferentialGeometry.Topology.VanKampen.standardConcat_quotient_eq

theorem standardSubpath_quotient_eq_refinement {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) {n k : ℕ} (hk : 0 < k) (i : Fin n) :
    Path.Homotopic.Quotient.mk (standardSubpath p i) =
      Path.Homotopic.Quotient.mk (standardConcat (standardSubpath p i) hk) :=
  (standardConcat_quotient_eq (standardSubpath p i) hk).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.VanKampen.standardSubpath_quotient_eq_refinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.VanKampen.standardSubpath_quotient_eq_refinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.VanKampen.standardSubpath_quotient_eq_refinement ``Submission.DifferentialGeometry.Topology.VanKampen.standardSubpath_quotient_eq_refinement

section Regression

example {X : Type u} [TopologicalSpace X] {a b : X} (p : Path a b) :
    Path.Homotopic.Quotient.mk (standardConcat p Nat.zero_lt_one) =
      Path.Homotopic.Quotient.mk p :=
  standardConcat_quotient_eq p Nat.zero_lt_one

end Regression

end DifferentialGeometry.Topology.VanKampen
