/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import Mathlib.Data.Sign.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem signType_cases_of_sign {a : ℝ} {s : SignType} :
    (SignType.sign a = s ∨ SignType.sign a = 0) ↔
      (s = 0 → a = 0) ∧ (s = 1 → 0 ≤ a) ∧ (s = -1 → a ≤ 0) := by
  rcases s with _ | _ | _
  · simp [sign_eq_zero_iff]
  · constructor
    · rintro (h | h)
      · exact ⟨fun h0 => by simp at h0, fun h1 => by simp at h1, fun _ => (sign_eq_neg_one_iff.mp
          h).le⟩
      · exact ⟨fun h0 => by simp at h0, fun h1 => by simp at h1, fun _ => (sign_eq_zero_iff.mp
          h).le⟩
    · rintro ⟨-, -, h⟩
      rcases (h rfl).lt_or_eq with h' | h'
      · exact Or.inl (sign_eq_neg_one_iff.mpr h')
      · exact Or.inr (sign_eq_zero_iff.mpr h')
  · constructor
    · rintro (h | h)
      · exact ⟨fun h0 => by simp at h0, fun _ => (sign_eq_one_iff.mp h).le, fun h1 => by simp at h1⟩
      · exact ⟨fun h0 => by simp at h0, fun _ => (sign_eq_zero_iff.mp h).ge,
          fun h1 => by simp at h1⟩
    · rintro ⟨-, h, -⟩
      rcases (h rfl).lt_or_eq with h' | h'
      · exact Or.inl (sign_eq_one_iff.mpr h')
      · exact Or.inr (sign_eq_zero_iff.mpr h'.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.signType_cases_of_sign then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.signType_cases_of_sign"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.signType_cases_of_sign ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.signType_cases_of_sign

theorem isClosed_setOf_imp {X : Type*} [TopologicalSpace X] (p : Prop) {q : X → Prop}
    (hq : IsClosed {y | q y}) : IsClosed {y | p → q y} := by
  by_cases hp : p
  · have h : {y : X | p → q y} = {y | q y} := by
      ext y
      simp [hp]
    rw [h]
    exact hq
  · have h : {y : X | p → q y} = univ := by
      ext y
      simp [hp]
    rw [h]
    exact isClosed_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_setOf_imp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isClosed_setOf_imp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_setOf_imp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isClosed_setOf_imp

theorem isOpen_setOf_imp {X : Type*} [TopologicalSpace X] (p : Prop) {q : X → Prop}
    (hq : IsOpen {y | q y}) : IsOpen {y | p → q y} := by
  by_cases hp : p
  · have h : {y : X | p → q y} = {y | q y} := by
      ext y
      simp [hp]
    rw [h]
    exact hq
  · have h : {y : X | p → q y} = univ := by
      ext y
      simp [hp]
    rw [h]
    exact isOpen_univ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_setOf_imp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOpen_setOf_imp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOpen_setOf_imp ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOpen_setOf_imp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Cells

variable {ι : Type*} (l : ι → E →ᵃ[ℝ] ℝ)

def SignLE (σ σ' : ι → SignType) : Prop := ∀ k, σ k = σ' k ∨ σ k = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SignLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SignLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SignLE ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SignLE

theorem SignLE.refl (σ : ι → SignType) : SignLE σ σ := fun _ => Or.inl rfl

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.SignLE
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SignLE.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SignLE.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SignLE.refl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SignLE.refl

theorem SignLE.trans {σ σ' σ'' : ι → SignType} (h : SignLE σ σ') (h' : SignLE σ' σ'') :
    SignLE σ σ'' := fun k => by
  rcases h k with h1 | h1
  · rw [h1]
    exact h' k
  · exact Or.inr h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SignLE.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SignLE.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SignLE.trans ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SignLE.trans

theorem SignLE.antisymm {σ σ' : ι → SignType} (h : SignLE σ σ') (h' : SignLE σ' σ) : σ = σ' := by
  funext k
  rcases h k with h1 | h1
  · exact h1
  · rcases h' k with h2 | h2
    · exact h2.symm
    · rw [h1, h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SignLE.antisymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SignLE.antisymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SignLE.antisymm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SignLE.antisymm

noncomputable def signVec (x : E) : ι → SignType := fun k => SignType.sign (l k x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.signVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.signVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.signVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.signVec

def openCell (σ : ι → SignType) : Set E := {y | signVec l y = σ}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.openCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.openCell

def closedCell (σ : ι → SignType) : Set E := {y | SignLE (signVec l y) σ}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedCell

theorem mem_openCell_iff {σ : ι → SignType} {y : E} : y ∈ openCell l σ ↔ signVec l y = σ := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_iff

theorem mem_closedCell_iff {σ : ι → SignType} {y : E} :
    y ∈ closedCell l σ ↔ SignLE (signVec l y) σ := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff

theorem mem_openCell_signVec (x : E) : x ∈ openCell l (signVec l x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_signVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_signVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_signVec ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_signVec

theorem openCell_subset_closedCell (σ : ι → SignType) : openCell l σ ⊆ closedCell l σ :=
  fun _ hy => hy ▸ SignLE.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.openCell_subset_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.openCell_subset_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.openCell_subset_closedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.openCell_subset_closedCell

theorem closedCell_mono {σ σ' : ι → SignType} (h : SignLE σ σ') :
    closedCell l σ ⊆ closedCell l σ' :=
  fun _ hy => SignLE.trans hy h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedCell_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedCell_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedCell_mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedCell_mono

theorem closedCell_signVec_subset {σ : ι → SignType} {y : E} (hy : y ∈ closedCell l σ) :
    closedCell l (signVec l y) ⊆ closedCell l σ :=
  closedCell_mono l hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedCell_signVec_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedCell_signVec_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedCell_signVec_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedCell_signVec_subset

theorem openCell_signVec_subset {σ : ι → SignType} {y : E} (hy : y ∈ closedCell l σ) :
    openCell l (signVec l y) ⊆ closedCell l σ :=
  (openCell_subset_closedCell l _).trans (closedCell_signVec_subset l hy)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.openCell_signVec_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.openCell_signVec_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.openCell_signVec_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.openCell_signVec_subset

theorem openCell_disjoint {σ σ' : ι → SignType} (h : σ ≠ σ') :
    Disjoint (openCell l σ) (openCell l σ') :=
  Set.disjoint_left.mpr fun _ hy hy' => h (hy.symm.trans hy')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.openCell_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.openCell_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.openCell_disjoint ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.openCell_disjoint

theorem signLE_of_openCell_subset_closedCell {σ σ' : ι → SignType} {x : E} (hx : x ∈ openCell l σ)
    (h : openCell l σ ⊆ closedCell l σ') : SignLE σ σ' :=
  hx ▸ h hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.signLE_of_openCell_subset_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.signLE_of_openCell_subset_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.signLE_of_openCell_subset_closedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.signLE_of_openCell_subset_closedCell

theorem mem_closedCell_iff_forall {σ : ι → SignType} {y : E} :
    y ∈ closedCell l σ ↔
      ∀ k, (σ k = 0 → l k y = 0) ∧ (σ k = 1 → 0 ≤ l k y) ∧ (σ k = -1 → l k y ≤ 0) := by
  simp only [mem_closedCell_iff, SignLE, signVec, signType_cases_of_sign]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff_forall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff_forall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff_forall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_closedCell_iff_forall

theorem eq_zero_of_mem_closedCell {σ : ι → SignType} {y : E} (hy : y ∈ closedCell l σ) {k : ι}
    (hk : σ k = 0) : l k y = 0 :=
  ((mem_closedCell_iff_forall l).mp hy k).1 hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eq_zero_of_mem_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eq_zero_of_mem_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eq_zero_of_mem_closedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eq_zero_of_mem_closedCell

theorem combo_mem_openCell {σ : ι → SignType} {p y : E} (hp : p ∈ openCell l σ)
    (hy : y ∈ closedCell l σ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p + b • y ∈ openCell l σ := by
  funext k
  have hpk : SignType.sign (l k p) = σ k := congrFun hp k
  have hyk := (mem_closedCell_iff_forall l).mp hy k
  change SignType.sign (l k (a • p + b • y)) = σ k
  rw [Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
  rcases hσ : σ k with _ | _ | _
  · rw [hσ] at hpk hyk
    rw [sign_eq_zero_iff.mp hpk, hyk.1 rfl]
    simp
  · rw [hσ] at hpk hyk
    have h1 := sign_eq_neg_one_iff.mp hpk
    have h2 := hyk.2.2 rfl
    exact sign_eq_neg_one_iff.mpr (by nlinarith)
  · rw [hσ] at hpk hyk
    have h1 := sign_eq_one_iff.mp hpk
    have h2 := hyk.2.1 rfl
    exact sign_eq_one_iff.mpr (by nlinarith)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.combo_mem_openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.combo_mem_openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.combo_mem_openCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.combo_mem_openCell

theorem convex_closedCell (σ : ι → SignType) : Convex ℝ (closedCell l σ) := by
  intro y hy y' hy' a b ha hb hab
  rw [mem_closedCell_iff_forall] at hy hy' ⊢
  intro k
  rw [Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
  obtain ⟨h0, h1, h2⟩ := hy k
  obtain ⟨h0', h1', h2'⟩ := hy' k
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h0 h, h0' h]
    ring
  · nlinarith [h1 h, h1' h]
  · nlinarith [h2 h, h2' h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.convex_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.convex_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.convex_closedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.convex_closedCell

theorem exists_ne_zero_eq_zero_of_notMem_openCell {σ : ι → SignType} {y : E}
    (hy : y ∈ closedCell l σ) (hyo : y ∉ openCell l σ) : ∃ k, σ k ≠ 0 ∧ l k y = 0 := by
  by_contra h
  push Not at h
  apply hyo
  funext k
  rcases hy k with h1 | h1
  · exact h1
  · by_cases hσ : σ k = 0
    · rw [hσ]
      exact h1
    · exact absurd (sign_eq_zero_iff.mp h1) (h k hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_ne_zero_eq_zero_of_notMem_openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_ne_zero_eq_zero_of_notMem_openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_ne_zero_eq_zero_of_notMem_openCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_ne_zero_eq_zero_of_notMem_openCell

theorem closedCell_subset_hyperplane {σ : ι → SignType} {k : ι} (hk : σ k = 0) :
    closedCell l σ ⊆ {y | l k y = 0} :=
  fun _ hy => eq_zero_of_mem_closedCell l hy hk

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedCell_subset_hyperplane then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedCell_subset_hyperplane"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedCell_subset_hyperplane ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedCell_subset_hyperplane

theorem mem_openCell_of_lt {σ : ι → SignType} {p x : E} (hp : p ∈ openCell l σ) {T T' : ℝ}
    (hT : 0 < T) (hlt : T < T') (hy' : p + T' • (x - p) ∈ closedCell l σ) :
    p + T • (x - p) ∈ openCell l σ := by
  have hT' : 0 < T' := hT.trans hlt
  have hcombo : p + T • (x - p) = (1 - T / T') • p + (T / T') • (p + T' • (x - p)) := by
    have hTT : T / T' * T' = T := div_mul_cancel₀ T hT'.ne'
    rw [smul_add, smul_smul, hTT, sub_smul, one_smul]
    abel
  rw [hcombo]
  exact combo_mem_openCell l hp hy' (by rw [sub_pos, div_lt_one hT']; exact hlt)
    (div_nonneg hT.le hT'.le) (by ring)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_of_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_openCell_of_lt

theorem exit_unique {σ : ι → SignType} {p x : E} (hp : p ∈ openCell l σ) {T T' : ℝ} (hT : 0 < T)
    (hT' : 0 < T') (hy : p + T • (x - p) ∈ closedCell l σ)
    (hy' : p + T' • (x - p) ∈ closedCell l σ) (hyo : p + T • (x - p) ∉ openCell l σ)
    (hyo' : p + T' • (x - p) ∉ openCell l σ) : T = T' := by
  rcases lt_trichotomy T T' with hlt | heq | hgt
  · exact absurd (mem_openCell_of_lt l hp hT hlt hy') hyo
  · exact heq
  · exact absurd (mem_openCell_of_lt l hp hT' hgt hy) hyo'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exit_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exit_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exit_unique ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exit_unique

variable [FiniteDimensional ℝ E]

theorem isClosed_closedCell (σ : ι → SignType) : IsClosed (closedCell l σ) := by
  have h : closedCell l σ = ⋂ k, ({y | σ k = 0 → l k y = 0} ∩ {y | σ k = 1 → 0 ≤ l k y} ∩
      {y | σ k = -1 → l k y ≤ 0}) := by
    ext y
    rw [mem_closedCell_iff_forall, _root_.Set.mem_iInter]
    refine forall_congr' fun k => ?_
    simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_ofPred_eq, and_assoc]
  rw [h]
  refine isClosed_iInter fun k => ?_
  have hc : Continuous (l k) := (l k).continuous_of_finiteDimensional
  exact ((isClosed_setOf_imp _ (isClosed_eq hc continuous_const)).inter
    (isClosed_setOf_imp _ (isClosed_le continuous_const hc))).inter
    (isClosed_setOf_imp _ (isClosed_le hc continuous_const))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_closedCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isClosed_closedCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isClosed_closedCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isClosed_closedCell

theorem exists_extension_of_mem_openCell [Finite ι] {σ : ι → SignType} {p y : E}
    (hp : p ∈ closedCell l σ) (hy : y ∈ openCell l σ) :
    ∃ δ > 0, ∀ t ∈ _root_.Set.Icc (0 : ℝ) δ, y + t • (y - p) ∈ openCell l σ := by
  let g : ι → ℝ → ℝ := fun k t => l k (y + t • (y - p))
  have hg : ∀ k, Continuous (g k) := fun k =>
    (l k).continuous_of_finiteDimensional.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hg0 : ∀ k, g k 0 = l k y := fun k => by simp [g]
  let U : Set ℝ := ⋂ k, ({t | σ k = 1 → 0 < g k t} ∩ {t | σ k = -1 → g k t < 0})
  have hU : IsOpen U :=
    isOpen_iInter_of_finite fun k =>
      (isOpen_setOf_imp _ (isOpen_lt continuous_const (hg k))).inter
        (isOpen_setOf_imp _ (isOpen_lt (hg k) continuous_const))
  have h0U : (0 : ℝ) ∈ U := by
    refine mem_iInter.mpr fun k => ?_
    have hyk : SignType.sign (l k y) = σ k := congrFun hy k
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [hg0]
      exact sign_eq_one_iff.mp (hyk.trans h1)
    · rw [hg0]
      exact sign_eq_neg_one_iff.mp (hyk.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  refine ⟨ε / 2, by positivity, fun t ht => ?_⟩
  have htU : t ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  have htk := mem_iInter.mp htU
  funext k
  change SignType.sign (g k t) = σ k
  rcases hσ : σ k with _ | _ | _
  · have hyk : l k y = 0 := eq_zero_of_mem_closedCell l (openCell_subset_closedCell l σ hy) hσ
    have hpk : l k p = 0 := eq_zero_of_mem_closedCell l hp hσ
    have hlin : (l k).linear (y - p) = 0 := by
      rw [← vsub_eq_sub, (l k).linearMap_vsub, hyk, hpk, vsub_eq_sub, sub_zero]
    have hg : g k t = 0 := by
      simp only [g]
      rw [add_comm, ← vadd_eq_add, (l k).map_vadd, vadd_eq_add, map_smul, hlin, smul_zero,
        zero_add, hyk]
    rw [hg]
    exact sign_zero
  · have h1 : σ k = -1 → g k t < 0 := (htk k).2
    exact sign_neg (h1 hσ)
  · have h1 : σ k = 1 → 0 < g k t := (htk k).1
    exact sign_pos (h1 hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_extension_of_mem_openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_extension_of_mem_openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_extension_of_mem_openCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_extension_of_mem_openCell

theorem exists_exit_of_mem_openCell [Finite ι] {σ : ι → SignType} (hc : IsCompact (closedCell l σ))
    {p x : E} (hp : p ∈ openCell l σ) (hx : x ∈ closedCell l σ) (hne : x ≠ p) :
    ∃ T : ℝ, 1 ≤ T ∧ p + T • (x - p) ∈ closedCell l σ ∧ p + T • (x - p) ∉ openCell l σ := by
  let S : Set ℝ := {t | p + t • (x - p) ∈ closedCell l σ}
  have hS_closed : IsClosed S :=
    (isClosed_closedCell l σ).preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hxp : 0 < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hS_bdd : BddAbove S := by
    obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall p
    refine ⟨R / ‖x - p‖, fun t ht => ?_⟩
    have h := hR ht
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
    rw [le_div_iff₀ hxp]
    exact (mul_le_mul_of_nonneg_right (le_abs_self t) hxp.le).trans h
  have h0 : (0 : ℝ) ∈ S := by
    change p + (0 : ℝ) • (x - p) ∈ closedCell l σ
    rw [zero_smul, add_zero]
    exact openCell_subset_closedCell l σ hp
  have h1 : (1 : ℝ) ∈ S := by
    change p + (1 : ℝ) • (x - p) ∈ closedCell l σ
    rw [one_smul, add_sub_cancel]
    exact hx
  have hT : _root_.SupSet.sSup S ∈ S := hS_closed.csSup_mem ⟨0, h0⟩ hS_bdd
  have hT1 : 1 ≤ _root_.SupSet.sSup S := le_csSup hS_bdd h1
  refine ⟨sSup S, hT1, hT, fun hTo => ?_⟩
  obtain ⟨δ, hδ, hext⟩ :=
    exists_extension_of_mem_openCell l (openCell_subset_closedCell l σ hp) hTo
  have hmem : _root_.SupSet.sSup S * (1 + δ) ∈ S := by
    have h := hext δ ⟨hδ.le, le_rfl⟩
    have heq : p + _root_.SupSet.sSup S • (x - p) + δ • (p + _root_.SupSet.sSup S • (x - p) - p) =
        p + (_root_.SupSet.sSup S * (1 + δ)) • (x - p) := by
      rw [add_sub_cancel_left, smul_smul, mul_comm δ, mul_add, mul_one, add_smul, add_assoc]
    rw [heq] at h
    exact openCell_subset_closedCell l σ h
  have := le_csSup hS_bdd hmem
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_exit_of_mem_openCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_exit_of_mem_openCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_exit_of_mem_openCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_exit_of_mem_openCell

end Cells

end DifferentialGeometry.Topology.PiecewiseLinear
