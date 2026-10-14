/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.NhdsWithin

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {N S : Set X}

theorem isOpen_preimage_closure_connectedComponentIn_of_local_separation
    (hSN : S ⊆ N)
    (hlocal : ∀ p ∈ S, ∃ C ∈ 𝓝[N] p, C ⊆ N ∧
      ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ S ∧
        C ∩ S ⊆ closure A ∧ C ∩ S ⊆ closure B) (x : X) :
    IsOpen (((↑) : S → X) ⁻¹' closure (connectedComponentIn (N \ S) x)) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨C, hC, hCN, A, B, hA, hB, hcover, htraceA, htraceB⟩ := hlocal p p.property
  obtain ⟨O, hO, hpO, hON⟩ := mem_nhdsWithin.mp hC
  obtain ⟨q, hqO, hq⟩ := (mem_closure_iff_nhds.mp hp) O (hO.mem_nhds hpO)
  have hqNS := connectedComponentIn_subset (N \ S) x hq
  have hqC : q ∈ C := hON ⟨hqO, hqNS.1⟩
  have hAsub : A ⊆ N \ S :=
    subset_union_left.trans (hcover.subset.trans (_root_.Set.sdiff_subset_sdiff_left hCN))
  have hBsub : B ⊆ N \ S :=
    subset_union_right.trans (hcover.subset.trans (_root_.Set.sdiff_subset_sdiff_left hCN))
  have htrace : C ∩ S ⊆ closure (connectedComponentIn (N \ S) x) := by
    rcases hcover.symm.subset ⟨hqC, hqNS.2⟩ with hqA | hqB
    · have hsub := hA.isPreconnected.subset_connectedComponentIn hqA hAsub
      rw [← connectedComponentIn_eq hq] at hsub
      exact htraceA.trans (closure_mono hsub)
    · have hsub := hB.isPreconnected.subset_connectedComponentIn hqB hBsub
      rw [← connectedComponentIn_eq hq] at hsub
      exact htraceB.trans (closure_mono hsub)
  exact Filter.mem_of_superset ((hO.preimage continuous_subtype_val).mem_nhds hpO)
    (fun z hz => htrace ⟨hON ⟨hz, hSN z.property⟩, z.property⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOpen_preimage_closure_connectedComponentIn_of_local_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOpen_preimage_closure_connectedComponentIn_of_local_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOpen_preimage_closure_connectedComponentIn_of_local_separation ``Submission.DifferentialGeometry.Topology.isOpen_preimage_closure_connectedComponentIn_of_local_separation

theorem subset_closure_connectedComponentIn_of_local_separation
    (hSN : S ⊆ N) (hS : IsPreconnected S)
    (hlocal : ∀ p ∈ S, ∃ C ∈ 𝓝[N] p, C ⊆ N ∧
      ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ S ∧
        C ∩ S ⊆ closure A ∧ C ∩ S ⊆ closure B) {x : X}
    (hne : (S ∩ closure (connectedComponentIn (N \ S) x)).Nonempty) :
    S ⊆ closure (connectedComponentIn (N \ S) x) := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hclopen : IsClopen (((↑) : S → X) ⁻¹' closure (connectedComponentIn (N \ S) x)) :=
    ⟨isClosed_closure.preimage continuous_subtype_val,
      isOpen_preimage_closure_connectedComponentIn_of_local_separation hSN hlocal x⟩
  obtain ⟨p, hpS, hp⟩ := hne
  have heq := hclopen.eq_univ ⟨⟨p, hpS⟩, hp⟩
  intro q hq
  exact congrArg (fun t : Set S => (⟨q, hq⟩ : S) ∈ t) heq.symm ▸ _root_.Set.mem_univ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subset_closure_connectedComponentIn_of_local_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subset_closure_connectedComponentIn_of_local_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subset_closure_connectedComponentIn_of_local_separation ``Submission.DifferentialGeometry.Topology.subset_closure_connectedComponentIn_of_local_separation

theorem exists_connectedComponentIn_pair_of_local_separation
    (hSN : S ⊆ N) (hS : IsConnected S)
    (hlocal : ∀ p ∈ S, ∃ C ∈ 𝓝[N] p, C ⊆ N ∧
      ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ S ∧
        C ∩ S ⊆ closure A ∧ C ∩ S ⊆ closure B) :
    ∃ a ∈ N \ S, ∃ b ∈ N \ S, ∀ x : X,
      (S ∩ closure (connectedComponentIn (N \ S) x)).Nonempty →
        connectedComponentIn (N \ S) x = connectedComponentIn (N \ S) a ∨
        connectedComponentIn (N \ S) x = connectedComponentIn (N \ S) b := by
  obtain ⟨p, hp⟩ := hS.nonempty
  obtain ⟨C, hC, hCN, A, B, hA, hB, hcover, -, -⟩ := hlocal p hp
  have hAsub : A ⊆ N \ S :=
    subset_union_left.trans (hcover.subset.trans (_root_.Set.sdiff_subset_sdiff_left hCN))
  have hBsub : B ⊆ N \ S :=
    subset_union_right.trans (hcover.subset.trans (_root_.Set.sdiff_subset_sdiff_left hCN))
  obtain ⟨a, ha⟩ := hA.nonempty
  obtain ⟨b, hb⟩ := hB.nonempty
  have hAcomp := hA.isPreconnected.subset_connectedComponentIn ha hAsub
  have hBcomp := hB.isPreconnected.subset_connectedComponentIn hb hBsub
  refine ⟨a, hAsub ha, b, hBsub hb, fun x hx => ?_⟩
  have hpcl := subset_closure_connectedComponentIn_of_local_separation hSN hS.isPreconnected
    hlocal hx hp
  obtain ⟨O, hO, hpO, hON⟩ := mem_nhdsWithin.mp hC
  obtain ⟨q, hqO, hq⟩ := (mem_closure_iff_nhds.mp hpcl) O (hO.mem_nhds hpO)
  have hqNS := connectedComponentIn_subset (N \ S) x hq
  have hqC : q ∈ C := hON ⟨hqO, hqNS.1⟩
  rcases hcover.symm.subset ⟨hqC, hqNS.2⟩ with hqA | hqB
  · exact Or.inl ((connectedComponentIn_eq hq).trans (connectedComponentIn_eq (hAcomp hqA)).symm)
  · exact Or.inr ((connectedComponentIn_eq hq).trans (connectedComponentIn_eq (hBcomp hqB)).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_connectedComponentIn_pair_of_local_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_connectedComponentIn_pair_of_local_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_connectedComponentIn_pair_of_local_separation ``Submission.DifferentialGeometry.Topology.exists_connectedComponentIn_pair_of_local_separation

theorem isOpen_preimage_connectedComponentIn_sdiff [LocallyConnectedSpace N]
    (hS : IsClosed S) (x : X) :
    IsOpen (((↑) : N → X) ⁻¹' connectedComponentIn (N \ S) x) := by
  let F : Set N := ((↑) : N → X) ⁻¹' Sᶜ
  have hF : IsOpen F := hS.isOpen_compl.preimage continuous_subtype_val
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hqF : q ∈ F := (connectedComponentIn_subset (N \ S) x hq).2
  apply Filter.mem_of_superset (connectedComponentIn_mem_nhds (hF.mem_nhds hqF))
  intro r hr
  have hpre : IsPreconnected (((↑) : N → X) '' connectedComponentIn F q) :=
    isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
  have hsub : ((↑) : N → X) '' connectedComponentIn F q ⊆ N \ S := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w.property, connectedComponentIn_subset F q hw⟩
  have hcomp := hpre.subset_connectedComponentIn
    (_root_.Set.mem_image_of_mem ((↑) : N → X) (mem_connectedComponentIn hqF)) hsub
  have hmem := hcomp (_root_.Set.mem_image_of_mem ((↑) : N → X) hr)
  rwa [← connectedComponentIn_eq hq] at hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isOpen_preimage_connectedComponentIn_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isOpen_preimage_connectedComponentIn_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isOpen_preimage_connectedComponentIn_sdiff ``Submission.DifferentialGeometry.Topology.isOpen_preimage_connectedComponentIn_sdiff

theorem inter_closure_connectedComponentIn_sdiff_nonempty [LocallyConnectedSpace N]
    (hN : IsPreconnected N) (hS : IsClosed S) (hSN : S ⊆ N) (hne : S.Nonempty)
    {x : X} (hx : x ∈ N \ S) :
    (S ∩ closure (connectedComponentIn (N \ S) x)).Nonempty := by
  by_contra h
  let A := connectedComponentIn (N \ S) x
  have hAsub : A ⊆ N \ S := connectedComponentIn_subset _ _
  have hAclsub : A ⊆ closure A ∩ N := fun z hz => ⟨subset_closure hz, (hAsub hz).1⟩
  have hclsub : closure A ∩ N ⊆ N \ S :=
    fun z hz => ⟨hz.2, fun hzS => h ⟨z, hzS, hz.1⟩⟩
  have hclpre : IsPreconnected (closure A ∩ N) :=
    isPreconnected_connectedComponentIn.subset_closure hAclsub _root_.Set.inter_subset_left
  have hcleq : closure A ∩ N = A :=
    Subset.antisymm
      (hclpre.subset_connectedComponentIn ⟨subset_closure (mem_connectedComponentIn hx), hx.1⟩
          hclsub)
      hAclsub
  have hpreimage : ((↑) : N → X) ⁻¹' closure A = ((↑) : N → X) ⁻¹' A := by
    ext z
    exact ⟨fun hz => hcleq.subset ⟨hz, z.property⟩, fun hz => subset_closure hz⟩
  have hclopen : IsClopen (((↑) : N → X) ⁻¹' A) :=
    ⟨hpreimage ▸ isClosed_closure.preimage continuous_subtype_val,
      isOpen_preimage_connectedComponentIn_sdiff hS x⟩
  let : PreconnectedSpace N := isPreconnected_iff_preconnectedSpace.mp hN
  have heq := hclopen.eq_univ ⟨⟨x, hx.1⟩, mem_connectedComponentIn hx⟩
  obtain ⟨p, hp⟩ := hne
  have hpA : (⟨p, hSN hp⟩ : N) ∈ ((↑) : N → X) ⁻¹' A := by
    rw [heq]
    exact _root_.Set.mem_univ _
  exact (hAsub hpA).2 hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.inter_closure_connectedComponentIn_sdiff_nonempty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.inter_closure_connectedComponentIn_sdiff_nonempty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.inter_closure_connectedComponentIn_sdiff_nonempty ``Submission.DifferentialGeometry.Topology.inter_closure_connectedComponentIn_sdiff_nonempty

theorem closure_connectedComponentIn_inter (T : Set X) (x : X) :
    closure (connectedComponentIn T x) ∩ T = connectedComponentIn T x := by
  by_cases hx : x ∈ T
  · have hsub : connectedComponentIn T x ⊆ closure (connectedComponentIn T x) ∩ T :=
      fun z hz => ⟨subset_closure hz, connectedComponentIn_subset T x hz⟩
    have hpre : IsPreconnected (closure (connectedComponentIn T x) ∩ T) :=
      isPreconnected_connectedComponentIn.subset_closure hsub _root_.Set.inter_subset_left
    exact Subset.antisymm
      (hpre.subset_connectedComponentIn ⟨subset_closure (mem_connectedComponentIn hx), hx⟩
        _root_.Set.inter_subset_right) hsub
  · rw [connectedComponentIn_eq_empty hx, closure_empty, _root_.Set.empty_inter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closure_connectedComponentIn_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closure_connectedComponentIn_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closure_connectedComponentIn_inter ``Submission.DifferentialGeometry.Topology.closure_connectedComponentIn_inter

theorem exists_connectedComponentIn_pair_sdiff_of_local_separation [LocallyConnectedSpace N]
    (hN : IsPreconnected N) (hNclosed : IsClosed N) (hS : IsConnected S) (hSclosed : IsClosed S)
    (hSN : S ⊆ N)
    (hlocal : ∀ p ∈ S, ∃ C ∈ 𝓝[N] p, C ⊆ N ∧
      ∃ A B : Set X, IsConnected A ∧ IsConnected B ∧ A ∪ B = C \ S ∧
        C ∩ S ⊆ closure A ∧ C ∩ S ⊆ closure B)
    (hsep : ¬IsPreconnected (N \ S)) :
    ∃ a ∈ N \ S, ∃ b ∈ N \ S,
      let A := connectedComponentIn (N \ S) a
      let B := connectedComponentIn (N \ S) b
      Disjoint A B ∧ A ∪ B = N \ S ∧ closure A ∪ closure B = N ∧ closure A ∩ closure B = S := by
  obtain ⟨a, ha, b, hb, hpair⟩ := exists_connectedComponentIn_pair_of_local_separation hSN hS hlocal
  have htouch (x : X) (hx : x ∈ N \ S) :
      (S ∩ closure (connectedComponentIn (N \ S) x)).Nonempty :=
    inter_closure_connectedComponentIn_sdiff_nonempty hN hSclosed hSN hS.nonempty hx
  let A := connectedComponentIn (N \ S) a
  let B := connectedComponentIn (N \ S) b
  have hAsub : A ⊆ N \ S := connectedComponentIn_subset _ _
  have hBsub : B ⊆ N \ S := connectedComponentIn_subset _ _
  have hunion : A ∪ B = N \ S := by
    apply Subset.antisymm (_root_.Set.union_subset hAsub hBsub)
    intro x hx
    rcases hpair x (htouch x hx) with hxa | hxb
    · exact Or.inl (hxa.subset (mem_connectedComponentIn hx))
    · exact Or.inr (hxb.subset (mem_connectedComponentIn hx))
  have hdisjoint : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hzA hzB
    have heq : A = B := (connectedComponentIn_eq hzA).trans (connectedComponentIn_eq hzB).symm
    apply hsep
    rw [← hunion, heq, _root_.Set.union_self]
    exact isPreconnected_connectedComponentIn
  have hSA : S ⊆ closure A :=
    subset_closure_connectedComponentIn_of_local_separation hSN hS.isPreconnected hlocal (htouch a
        ha)
  have hSB : S ⊆ closure B :=
    subset_closure_connectedComponentIn_of_local_separation hSN hS.isPreconnected hlocal (htouch b
        hb)
  have hAclN : closure A ⊆ N := closure_minimal (hAsub.trans _root_.Set.sdiff_subset) hNclosed
  have hBclN : closure B ⊆ N := closure_minimal (hBsub.trans _root_.Set.sdiff_subset) hNclosed
  refine ⟨a, ha, b, hb, hdisjoint, hunion, ?_, ?_⟩
  · apply Subset.antisymm (_root_.Set.union_subset hAclN hBclN)
    intro z hz
    by_cases hzS : z ∈ S
    · exact Or.inl (hSA hzS)
    · rcases hunion.symm.subset ⟨hz, hzS⟩ with hzA | hzB
      · exact Or.inl (subset_closure hzA)
      · exact Or.inr (subset_closure hzB)
  · apply Subset.antisymm _ (_root_.Set.subset_inter hSA hSB)
    rintro z ⟨hzA, hzB⟩
    by_contra hzS
    have hzNS : z ∈ N \ S := ⟨hAclN hzA, hzS⟩
    exact disjoint_left.mp hdisjoint
      ((closure_connectedComponentIn_inter (N \ S) a).subset ⟨hzA, hzNS⟩)
      ((closure_connectedComponentIn_inter (N \ S) b).subset ⟨hzB, hzNS⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_connectedComponentIn_pair_sdiff_of_local_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_connectedComponentIn_pair_sdiff_of_local_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_connectedComponentIn_pair_sdiff_of_local_separation ``Submission.DifferentialGeometry.Topology.exists_connectedComponentIn_pair_sdiff_of_local_separation

end DifferentialGeometry.Topology
