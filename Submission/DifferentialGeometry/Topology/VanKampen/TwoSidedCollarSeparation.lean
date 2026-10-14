/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Submission.DifferentialGeometry.Topology.VanKampen.CoverCycle

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Filter _root_.Topology

universe u v

namespace DifferentialGeometry.Topology.ThreeManifold

open _root_.Set
open _root_.Submission.DifferentialGeometry.Topology.VanKampen

structure TwoSidedCollar
    {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
    (e : S → X) where
  toFun : S × ℝ → X
  isOpenEmbedding_toFun : _root_.Topology.IsOpenEmbedding toFun
  zero_eq : ∀ s, toFun (s, 0) = e s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

namespace TwoSidedCollar

variable {S : Type v} [TopologicalSpace S] {X : Type u} [TopologicalSpace X]
  {e : S → X} (h : TwoSidedCollar e)

include h

theorem continuous_e : Continuous e := by
  have hp : Continuous (fun s : S => (s, (0 : ℝ))) := continuous_id.prodMk continuous_const
  rw [show e = fun s => h.toFun (s, 0) from funext fun s => (h.zero_eq s).symm]
  exact h.isOpenEmbedding_toFun.continuous.comp hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_e then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_e"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_e ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_e

theorem injective_e : Function.Injective e := by
  intro s t hst
  have hpairs : (s, (0 : ℝ)) = (t, 0) := by
    apply h.isOpenEmbedding_toFun.injective
    simpa only [h.zero_eq] using hst
  exact congrArg Prod.fst hpairs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.injective_e then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.injective_e"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.injective_e ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.injective_e

def complement (_h : TwoSidedCollar e) : Set X := (Set.range e)ᶜ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement

def range : Set X := Set.range h.toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range

theorem isOpen_range : IsOpen h.range :=
  h.isOpenEmbedding_toFun.isOpen_range

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_range ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_range

theorem isOpen_complement [CompactSpace S] [T2Space X] : IsOpen h.complement :=
  (isCompact_range h.continuous_e).isClosed.isOpen_compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_complement

theorem complement_union_range : h.complement ∪ h.range = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Set.range e
  · rcases hx with ⟨s, rfl⟩
    exact Or.inr ⟨(s, 0), h.zero_eq s⟩
  · exact Or.inl hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_range ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_range

noncomputable def homeomorphRange : S × ℝ ≃ₜ h.range :=
  h.isOpenEmbedding_toFun.toIsEmbedding.toHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.homeomorphRange then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.homeomorphRange"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.homeomorphRange ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.homeomorphRange

noncomputable def time (x : h.range) : ℝ :=
  (h.homeomorphRange.symm x).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time

theorem continuous_time : Continuous h.time :=
  continuous_snd.comp h.homeomorphRange.symm.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_time ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_time

@[simp]
theorem time_mk (p : S × ℝ) :
    h.time ⟨h.toFun p, ⟨p, rfl⟩⟩ = p.2 := by
  exact congrArg Prod.snd
    (h.isOpenEmbedding_toFun.toIsEmbedding.toHomeomorph_symm_apply p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_mk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_mk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_mk ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_mk

theorem mem_range_e_of_time_eq_zero (x : h.range) (hx : h.time x = 0) :
    x.1 ∈ Set.range e := by
  let p := h.homeomorphRange.symm x
  refine ⟨p.1, ?_⟩
  have hxp : h.toFun p = x.1 := by
    have := h.homeomorphRange.apply_symm_apply x
    exact congrArg Subtype.val this
  have hp2 : p.2 = 0 := by
    change (h.homeomorphRange.symm x).2 = 0
    exact hx
  calc
    e p.1 = h.toFun (p.1, 0) := (h.zero_eq p.1).symm
    _ = h.toFun p := congrArg h.toFun (Prod.ext rfl hp2.symm)
    _ = x.1 := hxp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.mem_range_e_of_time_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.mem_range_e_of_time_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.mem_range_e_of_time_eq_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.mem_range_e_of_time_eq_zero

theorem time_ne_zero_of_mem_complement (x : h.range) (hx : x.1 ∈ h.complement) :
    h.time x ≠ 0 := by
  intro ht
  exact hx (h.mem_range_e_of_time_eq_zero x ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_ne_zero_of_mem_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_ne_zero_of_mem_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_ne_zero_of_mem_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.time_ne_zero_of_mem_complement

theorem toFun_mem_complement_of_ne_zero (s : S) {t : ℝ} (ht : t ≠ 0) :
    h.toFun (s, t) ∈ h.complement := by
  intro hs
  rcases hs with ⟨s', hs'⟩
  have hpairs : (s, t) = (s', 0) := by
    apply h.isOpenEmbedding_toFun.injective
    simpa only [h.zero_eq] using hs'.symm
  exact ht (congrArg Prod.snd hpairs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_complement_of_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_complement_of_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_complement_of_ne_zero ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_complement_of_ne_zero

noncomputable def verticalPath (s : S) :
    Path (⟨h.toFun (s, -1), ⟨(s, -1), rfl⟩⟩ : h.range)
      ⟨h.toFun (s, 1), ⟨(s, 1), rfl⟩⟩ :=
  ((Path.refl s).prod (Path.segment (-1 : ℝ) 1)).map
    h.homeomorphRange.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.verticalPath then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.verticalPath"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.verticalPath ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.verticalPath

omit [TopologicalSpace S] [TopologicalSpace X] h in
theorem continuous_pos_iff_endpoints {f : unitInterval → ℝ}
    (hf : Continuous f) (hne : ∀ t, f t ≠ 0) :
    0 < f 0 ↔ 0 < f 1 := by
  constructor
  · intro hzero
    by_contra hone
    have hone' : f 1 < 0 := lt_of_le_of_ne (le_of_not_gt hone) (hne 1)
    have hz : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨hone'.le, hzero.le⟩
    rcases intermediate_value_univ (1 : unitInterval) (0 : unitInterval) hf hz with ⟨t, ht⟩
    exact hne t ht
  · intro hone
    by_contra hzero
    have hzero' : f 0 < 0 := lt_of_le_of_ne (le_of_not_gt hzero) (hne 0)
    have hz : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := ⟨hzero'.le, hone.le⟩
    rcases intermediate_value_univ (0 : unitInterval) (1 : unitInterval) hf hz with ⟨t, ht⟩
    exact hne t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_pos_iff_endpoints then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_pos_iff_endpoints"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_pos_iff_endpoints ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_pos_iff_endpoints

noncomputable def sideLabel (x : h.range) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (if 0 < h.time x then 1 else 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel

theorem sideLabel_constant_on_overlap_path
    (x y : ↑(h.complement ∩ h.range)) (p : Path x y) :
    h.sideLabel ⟨x.1, x.2.2⟩ = h.sideLabel ⟨y.1, y.2.2⟩ := by
  let pV : unitInterval → h.range := fun t => ⟨(p t).1, (p t).2.2⟩
  have hpV : Continuous pV :=
    (continuous_subtype_val.comp p.continuous).subtype_mk _
  have htime : Continuous (fun t => h.time (pV t)) := h.continuous_time.comp hpV
  have hne : ∀ t, h.time (pV t) ≠ 0 := fun t =>
    h.time_ne_zero_of_mem_complement (pV t) (p t).2.1
  have hsign := continuous_pos_iff_endpoints htime hne
  have hsign' : (0 < h.time ⟨x.1, x.2.2⟩) ↔
      0 < h.time ⟨y.1, y.2.2⟩ := by
    simpa only [pV, Path.source, Path.target] using hsign
  simp only [sideLabel]
  by_cases hx : 0 < h.time ⟨x.1, x.2.2⟩
  · rw [if_pos hx, if_pos (hsign'.mp hx)]
  · rw [if_neg hx, if_neg (fun hy => hx (hsign'.mpr hy))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel_constant_on_overlap_path then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel_constant_on_overlap_path"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel_constant_on_overlap_path ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.sideLabel_constant_on_overlap_path

theorem not_isConnected_complement
    [CompactSpace S] [Nonempty S] [T2Space X] [LocallyPathConnectedSpace X]
    [SimplyConnectedSpace X] :
    ¬ IsConnected h.complement := by
  intro hconnected
  let _ : ConnectedSpace h.complement := isConnected_iff_connectedSpace.mp hconnected
  let _ : LocallyPathConnectedSpace h.complement := h.isOpen_complement.locallyPathConnectedSpace
  let _ : PathConnectedSpace h.complement := PathConnectedSpace.of_locallyPathConnectedSpace
  let s : S := Classical.choice inferInstance
  let x₀ : X := h.toFun (s, -1)
  let x₁ : X := h.toFun (s, 1)
  have hx₀U : x₀ ∈ h.complement := h.toFun_mem_complement_of_ne_zero s (by norm_num)
  have hx₁U : x₁ ∈ h.complement := h.toFun_mem_complement_of_ne_zero s (by norm_num)
  have hx₀V : x₀ ∈ h.range := ⟨(s, -1), rfl⟩
  have hx₁V : x₁ ∈ h.range := ⟨(s, 1), rfl⟩
  let pU : Path (⟨x₀, hx₀U⟩ : h.complement) ⟨x₁, hx₁U⟩ :=
    PathConnectedSpace.somePath _ _
  let pV : Path (⟨x₀, hx₀V⟩ : h.range) ⟨x₁, hx₁V⟩ := h.verticalPath s
  have htime₀ : h.time ⟨x₀, hx₀V⟩ = -1 := by
    change h.time ⟨h.toFun (s, -1), _⟩ = -1
    exact h.time_mk (s, -1)
  have htime₁ : h.time ⟨x₁, hx₁V⟩ = 1 := by
    change h.time ⟨h.toFun (s, 1), _⟩ = 1
    exact h.time_mk (s, 1)
  exact (not_simplyConnectedSpace_of_cover_cycle
    h.complement h.range h.isOpen_complement h.isOpen_range h.complement_union_range
    x₀ x₁ hx₀U hx₁U hx₀V hx₁V pU pV h.sideLabel
    h.sideLabel_constant_on_overlap_path (by
      simp only [sideLabel, htime₀, htime₁, zero_lt_one, ↓reduceIte]
      norm_num)) inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.not_isConnected_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.not_isConnected_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.not_isConnected_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.not_isConnected_complement

noncomputable def negativePoint [Nonempty S] : h.complement :=
  let s : S := Classical.choice inferInstance
  ⟨h.toFun (s, -1), h.toFun_mem_complement_of_ne_zero s (by norm_num)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativePoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativePoint

noncomputable def positivePoint [Nonempty S] : h.complement :=
  let s : S := Classical.choice inferInstance
  ⟨h.toFun (s, 1), h.toFun_mem_complement_of_ne_zero s (by norm_num)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positivePoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positivePoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positivePoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positivePoint

theorem connectedComponent_meets_range
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (y : h.complement) :
    ∃ z ∈ connectedComponent y, z.1 ∈ h.range := by
  let _ : LocallyPathConnectedSpace h.complement :=
    h.isOpen_complement.locallyPathConnectedSpace
  let _ : LocallyConnectedSpace h.complement := inferInstance
  let C : Set h.complement := connectedComponent y
  by_contra hn
  push Not at hn
  let A : Set X := Subtype.val '' C
  let B : Set X := Subtype.val '' Cᶜ
  have hAopen : IsOpen A := h.isOpen_complement.isOpenMap_subtype_val C
    isOpen_connectedComponent
  have hBopen : IsOpen B := h.isOpen_complement.isOpenMap_subtype_val Cᶜ
    isClosed_connectedComponent.isOpen_compl
  have hcompl : Aᶜ = h.range ∪ B := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ h.complement ∪ h.range := by
        rw [h.complement_union_range]
        trivial
      rcases hxcover with hxU | hxV
      · refine Or.inr ⟨⟨x, hxU⟩, ?_, rfl⟩
        intro hC
        exact hx ⟨⟨x, hxU⟩, hC, rfl⟩
      · exact Or.inl hxV
    · rintro (hxV | ⟨z, hzC, rfl⟩)
      · intro hzA
        rcases hzA with ⟨z, hzC, hz⟩
        subst hz
        exact hn z hzC hxV
      · intro hzA
        rcases hzA with ⟨w, hwC, hwz⟩
        have hwz' : w = z := Subtype.ext hwz
        exact hzC (hwz' ▸ hwC)
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff, hcompl]
    exact h.isOpen_range.union hBopen
  have hAclopen : IsClopen A := ⟨hAclosed, hAopen⟩
  have hyA : y.1 ∈ A := ⟨y, mem_connectedComponent, rfl⟩
  have hAuniv : A = Set.univ := hAclopen.eq_univ ⟨y.1, hyA⟩
  let s : S := Classical.choice inferInstance
  have hzeroV : h.toFun (s, 0) ∈ h.range := ⟨(s, 0), rfl⟩
  have hzeroA : h.toFun (s, 0) ∈ A := hAuniv.symm ▸ Set.mem_univ _
  rcases hzeroA with ⟨z, hzC, hz⟩
  exact hn z hzC (hz.symm ▸ hzeroV)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponent_meets_range then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponent_meets_range"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponent_meets_range ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponent_meets_range

theorem component_eq_negative_or_positive
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] (y : h.complement) :
    ConnectedComponents.mk y = ConnectedComponents.mk h.negativePoint ∨
      ConnectedComponents.mk y = ConnectedComponents.mk h.positivePoint := by
  rcases h.connectedComponent_meets_range y with ⟨z, hzC, hzV⟩
  let zV : h.range := ⟨z.1, hzV⟩
  let p : S × ℝ := h.homeomorphRange.symm zV
  have hp : h.toFun p = z.1 := by
    exact congrArg Subtype.val (h.homeomorphRange.apply_symm_apply zV)
  have hpzero : p.2 ≠ 0 := by
    have ht : h.time zV ≠ 0 := h.time_ne_zero_of_mem_complement zV z.2
    change p.2 ≠ 0 at ht
    exact ht
  rcases lt_or_gt_of_ne hpzero with hpneg | hppos
  · left
    let _ : ConnectedSpace (Set.Iio (0 : ℝ)) :=
      isConnected_iff_connectedSpace.mp isConnected_Iio
    let f : S × Set.Iio (0 : ℝ) → h.complement := fun q =>
      ⟨h.toFun (q.1, q.2.1), h.toFun_mem_complement_of_ne_zero q.1 (ne_of_lt q.2.2)⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact h.isOpenEmbedding_toFun.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hfconn : IsConnected (Set.range f) := isConnected_range hf
    have hzrange : z ∈ Set.range f := by
      refine ⟨(p.1, ⟨p.2, hpneg⟩), ?_⟩
      exact Subtype.ext hp
    have hnrange : h.negativePoint ∈ Set.range f := by
      let s : S := Classical.choice inferInstance
      refine ⟨(s, ⟨-1, by norm_num⟩), ?_⟩
      rfl
    rw [ConnectedComponents.coe_eq_coe]
    exact (connectedComponent_eq hzC).trans
      (connectedComponent_eq (hfconn.subset_connectedComponent hnrange hzrange)).symm
  · right
    let _ : ConnectedSpace (Set.Ioi (0 : ℝ)) :=
      isConnected_iff_connectedSpace.mp isConnected_Ioi
    let f : S × Set.Ioi (0 : ℝ) → h.complement := fun q =>
      ⟨h.toFun (q.1, q.2.1), h.toFun_mem_complement_of_ne_zero q.1 (ne_of_gt q.2.2)⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact h.isOpenEmbedding_toFun.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have hfconn : IsConnected (Set.range f) := isConnected_range hf
    have hzrange : z ∈ Set.range f := by
      refine ⟨(p.1, ⟨p.2, hppos⟩), ?_⟩
      exact Subtype.ext hp
    have hprange : h.positivePoint ∈ Set.range f := by
      let s : S := Classical.choice inferInstance
      refine ⟨(s, ⟨1, by norm_num⟩), ?_⟩
      rfl
    rw [ConnectedComponents.coe_eq_coe]
    exact (connectedComponent_eq hzC).trans
      (connectedComponent_eq (hfconn.subset_connectedComponent hprange hzrange)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.component_eq_negative_or_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.component_eq_negative_or_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.component_eq_negative_or_positive ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.component_eq_negative_or_positive

theorem negative_component_ne_positive
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    ConnectedComponents.mk h.negativePoint ≠ ConnectedComponents.mk h.positivePoint := by
  intro hnp
  apply h.not_isConnected_complement
  rw [isConnected_iff_connectedSpace]
  let _ : Nonempty h.complement := ⟨h.negativePoint⟩
  let _ : PreconnectedSpace h.complement := preconnectedSpace_iff_connectedComponent.mpr (by
    intro y
    apply Set.eq_univ_of_forall
    intro z
    have hy := h.component_eq_negative_or_positive y
    have hz := h.component_eq_negative_or_positive z
    have hzy : ConnectedComponents.mk z = ConnectedComponents.mk y := by
      rcases hz with hz | hz <;> rcases hy with hy | hy
      · exact hz.trans hy.symm
      · exact hz.trans (hnp.trans hy.symm)
      · exact hz.trans (hnp.symm.trans hy.symm)
      · exact hz.trans hy.symm
    rw [← ConnectedComponents.coe_eq_coe.mp hzy]
    exact mem_connectedComponent)
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negative_component_ne_positive

noncomputable def connectedComponentsComplementEquivBool
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    ConnectedComponents h.complement ≃ Bool :=
  (Equiv.ofBijective
    (fun b : Bool => if b then ConnectedComponents.mk h.positivePoint
      else ConnectedComponents.mk h.negativePoint)
    ⟨by
      intro a b hab
      cases a <;> cases b
      · rfl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hab
        exact (h.negative_component_ne_positive hab).elim
      · simp only [↓reduceIte] at hab
        exact (h.negative_component_ne_positive hab.symm).elim
      · rfl,
     by
      intro c
      rcases ConnectedComponents.surjective_coe c with ⟨y, rfl⟩
      rcases h.component_eq_negative_or_positive y with hy | hy
      · exact ⟨false, by simpa using hy.symm⟩
      · exact ⟨true, by simpa using hy.symm⟩⟩).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponentsComplementEquivBool then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponentsComplementEquivBool"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponentsComplementEquivBool ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.connectedComponentsComplementEquivBool

noncomputable def negativeSide [Nonempty S] : Set X :=
  Subtype.val '' connectedComponent h.negativePoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide

noncomputable def positiveSide [Nonempty S] : Set X :=
  Subtype.val '' connectedComponent h.positivePoint

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide

theorem toFun_mem_negativeSide_of_neg [ConnectedSpace S] (s : S) {t : ℝ} (ht : t < 0) :
    h.toFun (s, t) ∈ h.negativeSide := by
  let _ : ConnectedSpace (Set.Iio (0 : ℝ)) :=
    isConnected_iff_connectedSpace.mp isConnected_Iio
  let f : S × Set.Iio (0 : ℝ) → h.complement := fun q =>
    ⟨h.toFun (q.1, q.2.1), h.toFun_mem_complement_of_ne_zero q.1 (ne_of_lt q.2.2)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact h.isOpenEmbedding_toFun.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfconn : IsConnected (Set.range f) := isConnected_range hf
  have htrange : f (s, ⟨t, ht⟩) ∈ Set.range f := ⟨_, rfl⟩
  have hnrange : h.negativePoint ∈ Set.range f := by
    let s₀ : S := Classical.choice inferInstance
    exact ⟨(s₀, ⟨-1, by norm_num⟩), rfl⟩
  exact ⟨f (s, ⟨t, ht⟩), hfconn.subset_connectedComponent hnrange htrange, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_of_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_of_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_of_neg ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_negativeSide_of_neg

theorem toFun_mem_positiveSide_of_pos [ConnectedSpace S] (s : S) {t : ℝ} (ht : 0 < t) :
    h.toFun (s, t) ∈ h.positiveSide := by
  let _ : ConnectedSpace (Set.Ioi (0 : ℝ)) :=
    isConnected_iff_connectedSpace.mp isConnected_Ioi
  let f : S × Set.Ioi (0 : ℝ) → h.complement := fun q =>
    ⟨h.toFun (q.1, q.2.1), h.toFun_mem_complement_of_ne_zero q.1 (ne_of_gt q.2.2)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact h.isOpenEmbedding_toFun.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hfconn : IsConnected (Set.range f) := isConnected_range hf
  have htrange : f (s, ⟨t, ht⟩) ∈ Set.range f := ⟨_, rfl⟩
  have hprange : h.positivePoint ∈ Set.range f := by
    let s₀ : S := Classical.choice inferInstance
    exact ⟨(s₀, ⟨1, by norm_num⟩), rfl⟩
  exact ⟨f (s, ⟨t, ht⟩), hfconn.subset_connectedComponent hprange htrange, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_of_pos ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_positiveSide_of_pos

theorem range_e_subset_closure_negativeSide [ConnectedSpace S] :
    Set.range e ⊆ closure h.negativeSide := by
  rintro _ ⟨s, rfl⟩
  rw [← h.zero_eq s]
  refine mem_closure_of_tendsto (f := fun t : ℝ => h.toFun (s, t))
    (b := nhdsWithin (0 : ℝ) (Set.Iio 0)) ?_ ?_
  · exact ((h.isOpenEmbedding_toFun.continuous.comp
      (continuous_const.prodMk continuous_id)).tendsto 0).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact h.toFun_mem_negativeSide_of_neg s ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_negativeSide

theorem range_e_subset_closure_positiveSide [ConnectedSpace S] :
    Set.range e ⊆ closure h.positiveSide := by
  rintro _ ⟨s, rfl⟩
  rw [← h.zero_eq s]
  refine mem_closure_of_tendsto (f := fun t : ℝ => h.toFun (s, t))
    (b := nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_ ?_
  · exact ((h.isOpenEmbedding_toFun.continuous.comp
      (continuous_const.prodMk continuous_id)).tendsto 0).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact h.toFun_mem_positiveSide_of_pos s ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.range_e_subset_closure_positiveSide

theorem negativeSide_subset_complement [Nonempty S] : h.negativeSide ⊆ h.complement := by
  rintro _ ⟨z, _, rfl⟩
  exact z.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide_subset_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide_subset_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide_subset_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.negativeSide_subset_complement

theorem positiveSide_subset_complement [Nonempty S] : h.positiveSide ⊆ h.complement := by
  rintro _ ⟨z, _, rfl⟩
  exact z.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide_subset_complement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide_subset_complement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide_subset_complement ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.positiveSide_subset_complement

theorem isOpen_negativeSide [CompactSpace S] [Nonempty S] [T2Space X]
    [LocallyPathConnectedSpace X] : IsOpen h.negativeSide := by
  let _ : LocallyPathConnectedSpace h.complement :=
    h.isOpen_complement.locallyPathConnectedSpace
  let _ : LocallyConnectedSpace h.complement := inferInstance
  exact h.isOpen_complement.isOpenMap_subtype_val _ isOpen_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_negativeSide

theorem isOpen_positiveSide [CompactSpace S] [Nonempty S] [T2Space X]
    [LocallyPathConnectedSpace X] : IsOpen h.positiveSide := by
  let _ : LocallyPathConnectedSpace h.complement :=
    h.isOpen_complement.locallyPathConnectedSpace
  let _ : LocallyConnectedSpace h.complement := inferInstance
  exact h.isOpen_complement.isOpenMap_subtype_val _ isOpen_connectedComponent

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.isOpen_positiveSide

theorem complement_eq_negativeSide_union_positiveSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] :
    h.complement = h.negativeSide ∪ h.positiveSide := by
  ext x
  constructor
  · intro hx
    let y : h.complement := ⟨x, hx⟩
    rcases h.component_eq_negative_or_positive y with hy | hy
    · exact Or.inl ⟨y, ConnectedComponents.coe_eq_coe'.mp hy, rfl⟩
    · exact Or.inr ⟨y, ConnectedComponents.coe_eq_coe'.mp hy, rfl⟩
  · rintro (hx | hx)
    · exact h.negativeSide_subset_complement hx
    · exact h.positiveSide_subset_complement hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_eq_negativeSide_union_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_eq_negativeSide_union_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_eq_negativeSide_union_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_eq_negativeSide_union_positiveSide

theorem disjoint_negativeSide_positiveSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    Disjoint h.negativeSide h.positiveSide := by
  rw [Set.disjoint_left]
  rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  have hab' : a = b := Subtype.ext hab.symm
  subst b
  have hccne : connectedComponent h.negativePoint ≠ connectedComponent h.positivePoint :=
    ConnectedComponents.coe_ne_coe.mp h.negative_component_ne_positive
  exact Set.disjoint_left.mp (connectedComponent_disjoint hccne) ha hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.disjoint_negativeSide_positiveSide

theorem complement_union_zeroSlice : h.complement ∪ Set.range e = Set.univ := by
  exact _root_.Set.compl_union_self (Set.range e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_zeroSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_zeroSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_zeroSlice ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complement_union_zeroSlice

theorem zeroSlice_disjoint_negativeSide [Nonempty S] :
    Disjoint (Set.range e) h.negativeSide := by
  rw [Set.disjoint_left]
  intro x hxz hxn
  exact h.negativeSide_subset_complement hxn hxz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_negativeSide

theorem zeroSlice_disjoint_positiveSide [Nonempty S] :
    Disjoint (Set.range e) h.positiveSide := by
  rw [Set.disjoint_left]
  intro x hxz hxp
  exact h.positiveSide_subset_complement hxp hxz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.zeroSlice_disjoint_positiveSide

theorem compl_negativeSide_union_zeroSlice
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    (h.negativeSide ∪ Set.range e)ᶜ = h.positiveSide := by
  ext x
  constructor
  · intro hx
    have hxZ : x ∉ Set.range e := fun hxe => hx (Or.inr hxe)
    have hxU : x ∈ h.complement := hxZ
    rw [h.complement_eq_negativeSide_union_positiveSide] at hxU
    exact hxU.resolve_left (fun hxn => hx (Or.inl hxn))
  · intro hxp hx
    rcases hx with hxn | hxz
    · exact Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hxn hxp
    · exact Set.disjoint_left.mp h.zeroSlice_disjoint_positiveSide hxz hxp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_negativeSide_union_zeroSlice

theorem compl_positiveSide_union_zeroSlice
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    (h.positiveSide ∪ Set.range e)ᶜ = h.negativeSide := by
  ext x
  constructor
  · intro hx
    have hxZ : x ∉ Set.range e := fun hxe => hx (Or.inr hxe)
    have hxU : x ∈ h.complement := hxZ
    rw [h.complement_eq_negativeSide_union_positiveSide] at hxU
    exact hxU.resolve_right (fun hxp => hx (Or.inl hxp))
  · intro hxn hx
    rcases hx with hxp | hxz
    · exact Set.disjoint_left.mp h.disjoint_negativeSide_positiveSide hxn hxp
    · exact Set.disjoint_left.mp h.zeroSlice_disjoint_negativeSide hxz hxn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.compl_positiveSide_union_zeroSlice

theorem closure_negativeSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    closure h.negativeSide = h.negativeSide ∪ Set.range e := by
  apply Set.Subset.antisymm
  · apply closure_minimal Set.subset_union_left
    rw [← isOpen_compl_iff, h.compl_negativeSide_union_zeroSlice]
    exact h.isOpen_positiveSide
  · exact Set.union_subset subset_closure h.range_e_subset_closure_negativeSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_negativeSide

theorem closure_positiveSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    closure h.positiveSide = h.positiveSide ∪ Set.range e := by
  apply Set.Subset.antisymm
  · apply closure_minimal Set.subset_union_left
    rw [← isOpen_compl_iff, h.compl_positiveSide_union_zeroSlice]
    exact h.isOpen_negativeSide
  · exact Set.union_subset subset_closure h.range_e_subset_closure_positiveSide

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.closure_positiveSide

theorem frontier_negativeSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    frontier h.negativeSide = Set.range e := by
  rw [h.isOpen_negativeSide.frontier_eq, h.closure_negativeSide]
  ext x
  constructor
  · rintro ⟨hxn | hxz, hnotn⟩
    · exact (hnotn hxn).elim
    · exact hxz
  · intro hxz
    exact ⟨Or.inr hxz, fun hxn =>
      Set.disjoint_left.mp h.zeroSlice_disjoint_negativeSide hxz hxn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_negativeSide

theorem frontier_positiveSide
    [CompactSpace S] [Nonempty S] [T2Space X] [ConnectedSpace S] [ConnectedSpace X]
    [LocallyPathConnectedSpace X] [SimplyConnectedSpace X] :
    frontier h.positiveSide = Set.range e := by
  rw [h.isOpen_positiveSide.frontier_eq, h.closure_positiveSide]
  ext x
  constructor
  · rintro ⟨hxp | hxz, hnotp⟩
    · exact (hnotp hxp).elim
    · exact hxz
  · intro hxz
    exact ⟨Or.inr hxz, fun hxp =>
      Set.disjoint_left.mp h.zeroSlice_disjoint_positiveSide hxz hxp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.frontier_positiveSide

end TwoSidedCollar

end DifferentialGeometry.Topology.ThreeManifold
