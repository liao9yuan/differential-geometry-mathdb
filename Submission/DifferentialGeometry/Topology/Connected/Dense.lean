/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Perfect

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology

theorem isPreconnected_of_dense_of_locally_preconnected_inter
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {S : Set X}
    (hS : Dense S)
    (hlocal : ∀ x : X, ∃ V ∈ 𝓝 x, IsPreconnected (V ∩ S)) :
    IsPreconnected S := by
  intro U V hU hV hcover hSU hSV
  have hsplit : (S ∩ U) ∪ (S ∩ V) = S := by
    rw [← _root_.Set.inter_union_distrib_left, inter_eq_left.mpr hcover]
  have hcoverClosure : (_root_.Set.univ : Set X) ⊆ closure (S ∩ U) ∪ closure (S ∩ V) := by
    rw [← closure_union, hsplit, hS.closure_eq]
  obtain ⟨p, hp⟩ := hSU
  obtain ⟨q, hq⟩ := hSV
  obtain ⟨x, _, hxU, hxV⟩ := isPreconnected_closed_iff.mp
    (_root_.PreconnectedSpace.isPreconnected_univ : IsPreconnected (_root_.Set.univ : Set X))
    (closure (S ∩ U)) (closure (S ∩ V)) isClosed_closure isClosed_closure
    hcoverClosure ⟨p, _root_.Set.mem_univ _, subset_closure hp⟩ ⟨q, _root_.Set.mem_univ _, subset_closure hq⟩
  obtain ⟨N, hN, hconn⟩ := hlocal x
  obtain ⟨y, hyN, hyS, hyU⟩ := mem_closure_iff_nhds.mp hxU N hN
  obtain ⟨z, hzN, hzS, hzV⟩ := mem_closure_iff_nhds.mp hxV N hN
  obtain ⟨w, hw, hwU, hwV⟩ := hconn U V hU hV
    (fun _ hw ↦ hcover hw.2) ⟨y, ⟨hyN, hyS⟩, hyU⟩ ⟨z, ⟨hzN, hzS⟩, hzV⟩
  exact ⟨w, hw.2, hwU, hwV⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPreconnected_of_dense_of_locally_preconnected_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPreconnected_of_dense_of_locally_preconnected_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPreconnected_of_dense_of_locally_preconnected_inter ``Submission.DifferentialGeometry.Topology.isPreconnected_of_dense_of_locally_preconnected_inter

theorem Preperfect.subset_closure_sdiff_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {C F : Set X} (hC : Preperfect C) (hF : F.Finite) : C ⊆ closure (C \ F) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro U hU
  have hN : (F \ {x})ᶜ ∈ 𝓝 x :=
    (hF.sdiff.isClosed.isOpen_compl).mem_nhds (by simp)
  obtain ⟨y, hy, hyx⟩ := (accPt_iff_nhds.mp (hC x hx)) (U ∩ (F \ {x})ᶜ)
    (Filter.inter_mem hU hN)
  refine ⟨y, hy.1.1, hy.2, ?_⟩
  intro hyF
  exact hy.1.2 ⟨hyF, hyx⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.Preperfect
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Preperfect.subset_closure_sdiff_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Preperfect.subset_closure_sdiff_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Preperfect.subset_closure_sdiff_finite ``Submission.DifferentialGeometry.Topology.Preperfect.subset_closure_sdiff_finite

theorem IsPreconnected.subset_closure_sdiff_finite {X : Type*}
    [TopologicalSpace X] [T1Space X] {C F : Set X}
    (hC : IsPreconnected C) (hne : C.Nontrivial) (hF : F.Finite) : C ⊆ closure (C \ F) :=
  Preperfect.subset_closure_sdiff_finite (hC.preperfect_of_nontrivial hne) hF

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.IsPreconnected
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsPreconnected.subset_closure_sdiff_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsPreconnected.subset_closure_sdiff_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsPreconnected.subset_closure_sdiff_finite ``Submission.DifferentialGeometry.Topology.IsPreconnected.subset_closure_sdiff_finite

end DifferentialGeometry.Topology
