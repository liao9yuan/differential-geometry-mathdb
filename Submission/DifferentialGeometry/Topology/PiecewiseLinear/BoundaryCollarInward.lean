/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.VanKampen.BoundaryCollarInjection
import Mathlib.Topology.Homotopy.Equiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.ContinuousMap

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {e : B → X} (c : TwoSidedCollar e)

private noncomputable def inwardValue (K : Set X) (q : unitInterval × K) : X := by
  classical
  exact if hx : q.2.val ∈ c.range then
    let p := c.homeomorphRange.symm ⟨q.2.val, hx⟩
    c.toFun (p.1, p.2 - q.1.val * _root_.Max.max 0 (1 + p.2))
  else q.2.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue target :: scope.openDecls } }

private theorem inwardValue_eq_of_outside_strip {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (q : unitInterval × K)
    (hq : q.2.val ∉ c.toFun '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-1 : ℝ) 0)) :
    c.inwardValue K q = q.2.val := by
  classical
  unfold inwardValue
  split_ifs with hx
  · let p := c.homeomorphRange.symm ⟨q.2.val, hx⟩
    have hp : c.toFun p = q.2.val :=
      congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨q.2.val, hx⟩)
    have ht : p.2 ≤ 0 := (hside p).mp (hp.symm ▸ q.2.property)
    have hlow : p.2 < -1 := by
      by_contra hn
      exact hq ⟨p, ⟨mem_univ _, le_of_not_gt hn, ht⟩, hp⟩
    change c.toFun (p.1, p.2 - q.1.val * _root_.Max.max 0 (1 + p.2)) = q.2.val
    rw [max_eq_left (by linarith), _root_.MulZeroClass.mul_zero, sub_zero]
    exact hp
  · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_eq_of_outside_strip
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_eq_of_outside_strip target :: scope.openDecls } }

private theorem continuous_inwardValue [CompactSpace B] [T2Space X] {K : Set X}
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) :
    Continuous (c.inwardValue K) := by
  let D := c.toFun '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-1 : ℝ) 0)
  have hDc : IsClosed D :=
    ((isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image c.isOpenEmbedding_toFun.continuous).isClosed
  let A : Set (unitInterval × K) := (fun q => q.2.val) ⁻¹' Dᶜ
  let C : Set (unitInterval × K) := (fun q => q.2.val) ⁻¹' c.range
  have hv : Continuous (fun q : unitInterval × K => q.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hA : IsOpen A := hDc.isOpen_compl.preimage hv
  have hC : IsOpen C := c.isOpen_range.preimage hv
  have hcover : A ∪ C = univ := by
    apply _root_.Set.eq_univ_of_forall
    intro q
    by_cases hq : q.2.val ∈ D
    · exact Or.inr (_root_.Set.image_subset_range _ _ hq)
    · exact Or.inl hq
  rw [← continuousOn_univ, ← hcover, continuousOn_union_iff_of_isOpen hA hC]
  constructor
  · exact hv.continuousOn.congr (fun q hq => c.inwardValue_eq_of_outside_strip hside q hq)
  · rw [continuousOn_iff_continuous_domRestrict]
    let j : C → c.range := fun q => ⟨q.val.2.val, q.property⟩
    have hj : Continuous j := (hv.comp continuous_subtype_val).subtype_mk _
    have hp := c.homeomorphRange.symm.continuous.comp hj
    have ht : Continuous (fun q : C => q.val.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    have hg : Continuous (fun q : C => c.toFun ((c.homeomorphRange.symm (j q)).1,
        (c.homeomorphRange.symm (j q)).2 -
          q.val.1.val * _root_.Max.max 0 (1 + (c.homeomorphRange.symm (j q)).2))) :=
      c.isOpenEmbedding_toFun.continuous.comp ((continuous_fst.comp hp).prodMk
        ((continuous_snd.comp hp).sub
          (ht.mul (continuous_const.max (continuous_const.add (continuous_snd.comp hp))))))
    exact hg.congr fun q => by
      classical
      change _ = c.inwardValue K q.val
      unfold inwardValue
      rw [dif_pos (show q.val.2.val ∈ c.range from q.property)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_inwardValue
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.continuous_inwardValue target :: scope.openDecls } }

private theorem toFun_mem_interior_of_neg {K : Set X}
    (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (p : B × ℝ) (hp : p.2 < 0) : c.toFun p ∈ interior K := by
  by_contra hi
  obtain ⟨b, hb⟩ := hfront ⟨subset_closure ((hside p).mpr hp.le), hi⟩
  have h := c.isOpenEmbedding_toFun.injective ((c.zero_eq b).trans hb)
  exact (ne_of_lt hp) (congrArg Prod.snd h).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_interior_of_neg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_mem_interior_of_neg target :: scope.openDecls } }

private theorem inwardValue_mem_interior_or_eq {K : Set X}
    (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) (q : unitInterval × K) :
    c.inwardValue K q ∈ interior K ∨ c.inwardValue K q = q.2.val := by
  classical
  unfold inwardValue
  split_ifs with hx
  · let p := c.homeomorphRange.symm ⟨q.2.val, hx⟩
    have hp : c.toFun p = q.2.val :=
      congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨q.2.val, hx⟩)
    have ht : p.2 ≤ 0 := (hside p).mp (hp.symm ▸ q.2.property)
    have hm : 0 ≤ q.1.val * _root_.Max.max 0 (1 + p.2) :=
      mul_nonneg q.1.property.1 (le_max_left _ _)
    by_cases hn : p.2 - q.1.val * _root_.Max.max 0 (1 + p.2) < 0
    · exact Or.inl (c.toFun_mem_interior_of_neg hfront hside _ hn)
    · right
      have heq : p.2 - q.1.val * _root_.Max.max 0 (1 + p.2) = p.2 := by linarith
      change c.toFun (p.1, p.2 - q.1.val * _root_.Max.max 0 (1 + p.2)) = q.2.val
      rw [heq]
      exact hp
  · exact Or.inr rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_mem_interior_or_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_mem_interior_or_eq target :: scope.openDecls } }

private theorem inwardValue_one_mem_interior {K : Set X}
    (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0) (x : K) :
    c.inwardValue K (1, x) ∈ interior K := by
  classical
  unfold inwardValue
  split_ifs with hx
  · apply c.toFun_mem_interior_of_neg hfront hside
    change (c.homeomorphRange.symm ⟨x.val, hx⟩).2 -
      (1 : ℝ) * _root_.Max.max 0 (1 + (c.homeomorphRange.symm ⟨x.val, hx⟩).2) < 0
    have := le_max_right (0 : ℝ) (1 + (c.homeomorphRange.symm ⟨x.val, hx⟩).2)
    linarith
  · by_contra hi
    obtain ⟨b, hb⟩ := hfront ⟨subset_closure x.property, hi⟩
    exact hx ⟨(b, 0), (c.zero_eq b).trans hb⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_one_mem_interior
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_one_mem_interior target :: scope.openDecls } }

private theorem inwardValue_zero (K : Set X) (x : K) :
    c.inwardValue K (0, x) = x.val := by
  classical
  unfold inwardValue
  split_ifs with hx
  · change c.toFun ((c.homeomorphRange.symm ⟨x.val, hx⟩).1,
      (c.homeomorphRange.symm ⟨x.val, hx⟩).2 -
        (0 : ℝ) * _root_.Max.max 0 (1 + (c.homeomorphRange.symm ⟨x.val, hx⟩).2)) = x.val
    simp only [_root_.MulZeroClass.zero_mul, sub_zero]
    exact congrArg Subtype.val (c.homeomorphRange.apply_symm_apply ⟨x.val, hx⟩)
  · rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.inwardValue_zero target :: scope.openDecls } }

noncomputable def intermediateDomainHomotopyEquiv [CompactSpace B] [T2Space X]
    {K A : Set X} (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hAi : interior K ⊆ A) (hAK : A ⊆ K) : A ≃ₕ K := by
  let i : C(A, K) := ⟨Set.inclusion hAK, continuous_inclusion hAK⟩
  let g : C(K, A) := ⟨fun x => ⟨c.inwardValue K (1, x),
      hAi (c.inwardValue_one_mem_interior hfront hside x)⟩,
    ((c.continuous_inwardValue hside).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  have hmA (q : unitInterval × A) : c.inwardValue K (q.1, i q.2) ∈ A := by
    rcases c.inwardValue_mem_interior_or_eq hfront hside (q.1, i q.2) with hi | he
    · exact hAi hi
    · exact he ▸ q.2.property
  have hmK (q : unitInterval × K) : c.inwardValue K q ∈ K := by
    rcases c.inwardValue_mem_interior_or_eq hfront hside q with hi | he
    · exact interior_subset hi
    · exact he ▸ q.2.property
  have hA : (ContinuousMap.id A).Homotopic (g.comp i) := by
    refine ⟨{
      toFun := fun q => ⟨c.inwardValue K (q.1, i q.2), hmA q⟩
      continuous_toFun := ((c.continuous_inwardValue hside).comp
        (continuous_fst.prodMk (i.continuous.comp continuous_snd))).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      exact Subtype.ext (c.inwardValue_zero K (Set.inclusion hAK x))
    · intro x
      rfl
  have hK : (ContinuousMap.id K).Homotopic (i.comp g) := by
    refine ⟨{
      toFun := fun q => ⟨c.inwardValue K q, hmK q⟩
      continuous_toFun := (c.continuous_inwardValue hside).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      exact Subtype.ext (c.inwardValue_zero K x)
    · intro x
      rfl
  exact ⟨i, g, hA.symm, hK.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv

theorem intermediateDomainHomotopyEquiv_apply [CompactSpace B] [T2Space X]
    {K A : Set X} (hfront : frontier K ⊆ Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ K ↔ p.2 ≤ 0)
    (hAi : interior K ⊆ A) (hAK : A ⊆ K) (x : A) :
    (c.intermediateDomainHomotopyEquiv hfront hside hAi hAK x : X) = x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intermediateDomainHomotopyEquiv_apply

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
