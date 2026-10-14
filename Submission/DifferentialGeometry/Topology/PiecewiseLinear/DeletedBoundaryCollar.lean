/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.CollaredCover

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar

variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
  {e : B → X} (c : TwoSidedCollar e)

private theorem toFun_notMem_of_base_notMem {G : Set X} (hG : G ⊆ Set.range e)
    (p : (e ⁻¹' Gᶜ) × ℝ) : c.toFun (p.1.val, p.2) ∉ G := by
  intro hp
  obtain ⟨b, hb⟩ := hG hp
  have h := c.isOpenEmbedding_toFun.injective ((c.zero_eq b).trans hb)
  have he : b = p.1.val := congrArg Prod.fst h
  apply p.1.property
  rw [← he]
  exact hb.symm ▸ hp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_notMem_of_base_notMem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.toFun_notMem_of_base_notMem target :: scope.openDecls } }

def complementRestriction {G : Set X} (hGc : IsClosed G) (hG : G ⊆ Set.range e) :
    TwoSidedCollar (fun b : e ⁻¹' Gᶜ => (⟨e b.val, b.property⟩ : (Gᶜ : Set X))) where
  toFun p := ⟨c.toFun (p.1.val, p.2), c.toFun_notMem_of_base_notMem hG p⟩
  isOpenEmbedding_toFun := by
    have hbase := (hGc.isOpen_compl.preimage c.continuous_e).isOpenEmbedding_subtypeVal
    have hp := c.isOpenEmbedding_toFun.comp (hbase.prodMap .id)
    exact .of_isEmbedding_isOpenMap
      (hp.isEmbedding.codRestrict Gᶜ (c.toFun_notMem_of_base_notMem hG))
      (hp.isOpenMap.codRestrict (c.toFun_notMem_of_base_notMem hG))
  zero_eq b := Subtype.ext (c.zero_eq b.val)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction

theorem complementRestriction_toFun {G : Set X} (hGc : IsClosed G)
    (hG : G ⊆ Set.range e) (p : (e ⁻¹' Gᶜ) × ℝ) :
    ((c.complementRestriction hGc hG).toFun p : X) = c.toFun (p.1.val, p.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction_toFun ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.complementRestriction_toFun

include c in
theorem exists_open_cover_of_deleted_closed_cover {P Q G : Set X}
    (hGc : IsClosed G) (hG : G ⊆ Set.range e) [ConnectedSpace (e ⁻¹' Gᶜ)]
    (hcover : P ∪ Q = _root_.Set.univ) (hmeet : P ∩ Q = Set.range e)
    (hPcl : closure (P \ Q) = P) (hQcl : closure (Q \ P) = Q) :
    ∃ d : TwoSidedCollar (fun b : e ⁻¹' Gᶜ =>
      (⟨e b.val, b.property⟩ : (Gᶜ : Set X))),
      (∀ p, d.toFun p ∈ Subtype.val ⁻¹' P ↔ p.2 ≤ 0) ∧
      (∀ p, d.reverse.toFun p ∈ Subtype.val ⁻¹' Q ↔ p.2 ≤ 0) ∧
      d.domainNeighborhood (Subtype.val ⁻¹' P) ∪
        d.reverse.domainNeighborhood (Subtype.val ⁻¹' Q) = _root_.Set.univ ∧
      d.domainNeighborhood (Subtype.val ⁻¹' P) ∩
        d.reverse.domainNeighborhood (Subtype.val ⁻¹' Q) = d.range := by
  have hco := hGc.isOpen_compl.isOpenEmbedding_subtypeVal
  have hcover' : ((↑) : (Gᶜ : Set X) → X) ⁻¹' P ∪ Subtype.val ⁻¹' Q = univ := by
    rw [← _root_.Set.preimage_union, hcover, _root_.Set.preimage_univ]
  have hmeet' : ((↑) : (Gᶜ : Set X) → X) ⁻¹' P ∩ Subtype.val ⁻¹' Q =
      Set.range (fun b : e ⁻¹' Gᶜ => (⟨e b.val, b.property⟩ : (Gᶜ : Set X))) := by
    rw [← _root_.Set.preimage_inter, hmeet]
    ext x
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨⟨b, show e b ∈ Gᶜ from hb.symm ▸ x.property⟩, Subtype.ext hb⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b.val, rfl⟩
  have hPcl' : closure (((↑) : (Gᶜ : Set X) → X) ⁻¹' P \ Subtype.val ⁻¹' Q) =
      Subtype.val ⁻¹' P := by
    rw [← _root_.Set.preimage_sdiff, ← hco.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hPcl]
  have hQcl' : closure (((↑) : (Gᶜ : Set X) → X) ⁻¹' Q \ Subtype.val ⁻¹' P) =
      Subtype.val ⁻¹' Q := by
    rw [← _root_.Set.preimage_sdiff, ← hco.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hQcl]
  obtain ⟨d, _, hdP, hdQ, hU, hI⟩ :=
    (c.complementRestriction hGc hG).exists_open_cover_of_closed_cover
      hcover' hmeet' hPcl' hQcl'
  exact ⟨d, hdP, hdQ, hU, hI⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_open_cover_of_deleted_closed_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_open_cover_of_deleted_closed_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_open_cover_of_deleted_closed_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar.exists_open_cover_of_deleted_closed_cover

end DifferentialGeometry.Topology.ThreeManifold.TwoSidedCollar
