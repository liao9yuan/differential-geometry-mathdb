/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.BicollaredComplement
import Submission.DifferentialGeometry.Topology.Homeomorph.ClosedExtension
import Submission.DifferentialGeometry.Topology.VanKampen.BoundaryCollarOrientation
import Submission.DifferentialGeometry.Topology.VanKampen.BoundaryCollarRestriction
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

private noncomputable def intervalExpansion : _root_.Set.Icc (-1 : ℝ) 1 ≃ₜ _root_.Set.Icc (-1 : ℝ) 1 where
  toFun t := ⟨min ((3 * t + 1) / 2) ((t + 1) / 2), by
    constructor
    · apply le_min <;> linarith [t.property.1]
    · exact (min_le_right _ _).trans (by linarith [t.property.2])⟩
  invFun t := ⟨max ((2 * t - 1) / 3) (2 * t - 1), by
    constructor
    · exact (by linarith [t.property.1] : -1 ≤ (2 * (t : ℝ) - 1) / 3).trans
        (le_max_left _ _)
    · apply max_le <;> linarith [t.property.2]⟩
  left_inv t := by
    apply Subtype.ext
    change _root_.Max.max ((2 * _root_.Min.min ((3 * (t : ℝ) + 1) / 2) ((t + 1) / 2) - 1) / 3)
      (2 * _root_.Min.min ((3 * (t : ℝ) + 1) / 2) ((t + 1) / 2) - 1) = t
    by_cases ht : (t : ℝ) ≤ 0
    · rw [min_eq_left (by linarith)]
      rw [max_eq_left (by linarith)]
      ring
    · rw [min_eq_right (by linarith)]
      rw [max_eq_right (by linarith)]
      ring
  right_inv t := by
    apply Subtype.ext
    change _root_.Min.min ((3 * _root_.Max.max ((2 * (t : ℝ) - 1) / 3) (2 * t - 1) + 1) / 2)
      ((_root_.Max.max ((2 * (t : ℝ) - 1) / 3) (2 * t - 1) + 1) / 2) = t
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · rw [max_eq_left (by linarith)]
      rw [min_eq_left (by linarith)]
      ring
    · rw [max_eq_right (by linarith)]
      rw [min_eq_right (by linarith)]
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intervalExpansion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intervalExpansion target :: scope.openDecls } }

private theorem intervalExpansion_endpoints (t : _root_.Set.Icc (-1 : ℝ) 1)
    (ht : (t : ℝ) = -1 ∨ (t : ℝ) = 1) : intervalExpansion t = t := by
  apply Subtype.ext
  change _root_.Min.min ((3 * (t : ℝ) + 1) / 2) ((t + 1) / 2) = t
  rcases ht with ht | ht <;> rw [ht] <;> norm_num

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intervalExpansion_endpoints
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intervalExpansion_endpoints target :: scope.openDecls } }

private theorem intervalExpansion_neg_of_nonpos (t : _root_.Set.Icc (-1 : ℝ) 1)
    (ht : (intervalExpansion t : ℝ) ≤ 0) : (t : ℝ) < 0 := by
  change _root_.Min.min ((3 * (t : ℝ) + 1) / 2) ((t + 1) / 2) ≤ 0 at ht
  rcases min_le_iff.mp ht with ht | ht <;> linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intervalExpansion_neg_of_nonpos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.intervalExpansion_neg_of_nonpos target :: scope.openDecls } }

variable {B X : Type*} [TopologicalSpace B] [CompactSpace B]
  [TopologicalSpace X] [T2Space X] {e : B → X}

private theorem exists_homeomorph_outward (c : TwoSidedCollar e) {N : Set X}
    (hfront : frontier N = Set.range e)
    (hside : ∀ p : B × ℝ, c.toFun p ∈ N ↔ p.2 ≤ 0) :
    ∃ H : X ≃ₜ X, N ⊆ interior (H '' N) ∧
      H '' N ⊆ N ∪ c.range ∧ ∀ x ∉ c.range, H x = x := by
  let f : B × _root_.Set.Icc (-1 : ℝ) 1 → X := fun q => c.toFun (q.1, q.2)
  have hf : _root_.Topology.IsEmbedding f := c.isOpenEmbedding_toFun.isEmbedding.comp
    (IsEmbedding.id.prodMap IsEmbedding.subtypeVal)
  let W := Set.range f
  have hW : IsCompact W := isCompact_range hf.continuous
  let k : B × _root_.Set.Icc (-1 : ℝ) 1 ≃ₜ W := hf.toHomeomorph
  let d : W ≃ₜ W := (k.symm.trans ((Homeomorph.refl B).prodCongr intervalExpansion)).trans k
  have hWc : W ⊆ c.range := by
    rintro x ⟨q, rfl⟩
    exact ⟨(q.1, q.2), rfl⟩
  have hdf (q : B × _root_.Set.Icc (-1 : ℝ) 1) :
      (d (k q) : X) = c.toFun (q.1, intervalExpansion q.2) := by
    simp only [d, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rfl
  have hfrontW : ∀ q : B × _root_.Set.Icc (-1 : ℝ) 1,
      f q ∈ frontier W → (q.2 : ℝ) = -1 ∨ (q.2 : ℝ) = 1 := by
    intro q hq
    by_contra hne
    have ht : (q.2 : ℝ) ∈ _root_.Set.Ioo (-1 : ℝ) 1 := by
      push Not at hne
      exact ⟨lt_of_le_of_ne q.2.property.1 hne.1.symm,
        lt_of_le_of_ne q.2.property.2 hne.2⟩
    have hopen : IsOpen (c.toFun '' ((_root_.Set.univ : Set B) ×ˢ _root_.Set.Ioo (-1 : ℝ) 1)) :=
      c.isOpenEmbedding_toFun.isOpenMap _ (isOpen_univ.prod isOpen_Ioo)
    have hsub : c.toFun '' ((_root_.Set.univ : Set B) ×ˢ _root_.Set.Ioo (-1 : ℝ) 1) ⊆ W := by
      rintro x ⟨⟨b, t⟩, ht, rfl⟩
      exact ⟨(b, ⟨t, ht.2.1.le, ht.2.2.le⟩), rfl⟩
    exact hq.2 (interior_maximal hsub hopen ⟨(q.1, q.2), ⟨mem_univ _, ht⟩, rfl⟩)
  have hdfix : ∀ x : W, (x : X) ∈ frontier W → d x = x := by
    intro x hx
    obtain ⟨q, rfl⟩ := k.surjective x
    apply Subtype.ext
    rw [hdf, intervalExpansion_endpoints q.2 (hfrontW q hx)]
    rfl
  let H : X ≃ₜ X := d.extendById hW.isClosed hdfix
  have hHf (q : B × _root_.Set.Icc (-1 : ℝ) 1) :
      H (f q) = c.toFun (q.1, intervalExpansion q.2) := by
    rw [Homeomorph.extendById_apply_of_mem d hW.isClosed hdfix (_root_.Set.mem_range_self q)]
    exact hdf q
  have hHfix (x : X) (hx : x ∉ W) : H x = x :=
    d.extendById_apply_of_notMem hW.isClosed hdfix hx
  have hneg (p : B × ℝ) (hp : p.2 < 0) : c.toFun p ∈ interior N := by
    apply interior_maximal (t := c.toFun '' ((_root_.Set.univ : Set B) ×ˢ _root_.Set.Iio (0 : ℝ)))
    · rintro x ⟨q, hq, rfl⟩
      exact (hside q).mpr hq.2.le
    · exact c.isOpenEmbedding_toFun.isOpenMap _ (isOpen_univ.prod isOpen_Iio)
    · exact ⟨p, ⟨mem_univ _, hp⟩, rfl⟩
  refine ⟨H, ?_, ?_, fun x hx => hHfix x (fun h => hx (hWc h))⟩
  · intro x hx
    rw [← H.image_interior]
    refine ⟨H.symm x, ?_, H.apply_symm_apply x⟩
    by_cases hy : H.symm x ∈ W
    · obtain ⟨q, hq⟩ := hy
      have hxeq : x = c.toFun (q.1, intervalExpansion q.2) := by
        rw [← hHf, hq, H.apply_symm_apply]
      have ht := (hside (q.1, (intervalExpansion q.2 : ℝ))).mp (hxeq ▸ hx)
      rw [← hq]
      exact hneg (q.1, q.2) (intervalExpansion_neg_of_nonpos q.2 ht)
    · have heq : H.symm x = x := by
        have h := hHfix (H.symm x) hy
        rw [H.apply_symm_apply] at h
        exact h.symm
      rw [heq]
      by_contra hxi
      have hxf : x ∈ frontier N := ⟨subset_closure hx, hxi⟩
      obtain ⟨b, hb⟩ := hfront ▸ hxf
      apply hy
      rw [heq, ← hb]
      exact ⟨(b, ⟨0, by norm_num⟩), c.zero_eq b⟩
  · rintro x ⟨y, hyN, rfl⟩
    by_cases hyW : y ∈ W
    · right
      obtain ⟨q, rfl⟩ := hyW
      rw [hHf]
      exact ⟨(q.1, intervalExpansion q.2), rfl⟩
    · left
      rwa [hHfix y hyW]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_homeomorph_outward
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_homeomorph_outward target :: scope.openDecls } }

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem IsBicollared.exists_thickening_fixed_on_closed {N A U : Set X}
    (hbi : IsBicollared (frontier N))
    (hregular : closure (interior N) = N) (hconn : IsConnected (frontier N))
    (hcompact : IsCompact (frontier N)) (hA : IsClosed A) (hAN : A ⊆ interior N)
    (hU : IsOpen U) (hNU : N ⊆ U) :
    ∃ P : Set X, P ⊆ U ∧ N ⊆ interior P ∧
      ∃ e : N ≃ₜ P, ∀ x : N, (x : X) ∈ A → (e x : X) = (x : X) := by
  let _ : CompactSpace (frontier N) := isCompact_iff_compactSpace.mp hcompact
  let _ : ConnectedSpace (frontier N) := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨c⟩ := hbi
  have hclosed : IsClosed N := hregular ▸ isClosed_closure
  have hfrontU : Set.range (Subtype.val : frontier N → X) ⊆ U \ A := by
    rw [Subtype.range_coe]
    intro x hx
    exact ⟨hNU (hclosed.frontier_subset hx),
      fun hxA => disjoint_left.mp disjoint_interior_frontier (hAN hxA) hx⟩
  obtain ⟨d, hdU, -⟩ := c.exists_subcollar_subset_open (hU.sdiff hA) hfrontU
  have hdfront (p : frontier N × ℝ) : d.toFun p ∈ frontier N ↔ p.2 = 0 := by
    apply d.frontier_zero_of_disjoint_rest (R := ∅)
    · simp only [Subtype.range_coe, _root_.Set.union_empty]
    · exact _root_.Set.disjoint_empty _
  obtain ⟨g, hgd, hgside⟩ := d.exists_outward_collar_of_frontier_zero hregular hdfront
  obtain ⟨H, hHN, hHsub, hHfix⟩ := ThreeManifold.TwoSidedCollar.exists_homeomorph_outward g
    (by rw [Subtype.range_coe]) hgside
  refine ⟨H '' N, hHsub.trans (_root_.Set.union_subset hNU ((hgd.trans hdU).trans _root_.Set.sdiff_subset)),
    hHN, H.image N, ?_⟩
  intro x hx
  exact hHfix x (fun hxg => (hdU (hgd hxg)).2 hx)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.IsBicollared
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsBicollared.exists_thickening_fixed_on_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsBicollared.exists_thickening_fixed_on_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsBicollared.exists_thickening_fixed_on_closed ``Submission.DifferentialGeometry.Topology.IsBicollared.exists_thickening_fixed_on_closed

end DifferentialGeometry.Topology
