/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.HasGroupoid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open scoped _root_.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {H X : Type*} [TopologicalSpace H] [TopologicalSpace X]

theorem ofSet_mem_of_closedUnderRestriction (G : StructureGroupoid H) [ClosedUnderRestriction G]
    {s : Set H} (hs : IsOpen s) : OpenPartialHomeomorph.ofSet s hs ∈ G :=
  StructureGroupoid.le_iff.mp ((closedUnderRestriction_iff_id_le G).mp inferInstance) _
    (idRestrGroupoid_mem hs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.ofSet_mem_of_closedUnderRestriction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.ofSet_mem_of_closedUnderRestriction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.ofSet_mem_of_closedUnderRestriction ``Submission.DifferentialGeometry.Topology.Manifold.ofSet_mem_of_closedUnderRestriction

structure AtlasOn (G : StructureGroupoid H) (U : Set X) where
  charts : Set (OpenPartialHomeomorph X H)
  source_subset : ∀ e ∈ charts, e.source ⊆ U
  exists_mem_source : ∀ x ∈ U, ∃ e ∈ charts, x ∈ e.source
  compatible : ∀ e ∈ charts, ∀ e' ∈ charts, e.symm ≫ₕ e' ∈ G

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn

namespace AtlasOn

variable {G : StructureGroupoid H} {U V : Set X}

def congr (A : AtlasOn G U) (h : U = V) : AtlasOn G V where
  charts := A.charts
  source_subset e he := h ▸ A.source_subset e he
  exists_mem_source x hx := A.exists_mem_source x (h ▸ hx)
  compatible := A.compatible

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.congr ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.congr

def empty (G : StructureGroupoid H) : AtlasOn G (∅ : Set X) where
  charts := ∅
  source_subset _ he := absurd he (_root_.Set.notMem_empty _)
  exists_mem_source _ hx := absurd hx (_root_.Set.notMem_empty _)
  compatible _ he := absurd he (_root_.Set.notMem_empty _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.empty ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.empty

def ofOpenPartialHomeomorph [ClosedUnderRestriction G] (e : OpenPartialHomeomorph X H) :
    AtlasOn G e.source where
  charts := {e}
  source_subset e' he' := by
    rw [_root_.Set.mem_singleton_iff] at he'
    rw [he']
  exists_mem_source x hx := ⟨e, rfl, hx⟩
  compatible e₁ he₁ e₂ he₂ := by
    rw [_root_.Set.mem_singleton_iff] at he₁ he₂
    rw [he₁, he₂]
    exact G.mem_of_eqOnSource (ofSet_mem_of_closedUnderRestriction G e.open_target)
      e.symm_trans_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.ofOpenPartialHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.ofOpenPartialHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.ofOpenPartialHomeomorph ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.ofOpenPartialHomeomorph

theorem restrOpen_target (e : OpenPartialHomeomorph X H) (hV : IsOpen V) :
    (e.restrOpen V hV).target = e.target ∩ e.symm ⁻¹' V := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.restrOpen_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.restrOpen_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.restrOpen_target ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.restrOpen_target

def restrict [ClosedUnderRestriction G] (A : AtlasOn G U) (hV : IsOpen V) :
    AtlasOn G (U ∩ V) where
  charts := (fun e => e.restrOpen V hV) '' A.charts
  source_subset := by
    rintro _ ⟨e, he, rfl⟩
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact _root_.Set.inter_subset_inter_left _ (A.source_subset e he)
  exists_mem_source x hx := by
    obtain ⟨e, he, hxe⟩ := A.exists_mem_source x hx.1
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hxe, hx.2⟩
  compatible := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    have hopen : IsOpen (e.target ∩ e.symm ⁻¹' V) :=
      e.continuousOn_symm.isOpen_inter_preimage e.open_target hV
    refine G.mem_of_eqOnSource (closedUnderRestriction' (A.compatible e he e' he') hopen) ?_
    change (e.restrOpen V hV).symm ≫ₕ e'.restrOpen V hV ≈
      (e.symm ≫ₕ e').restr (e.target ∩ e.symm ⁻¹' V)
    refine ⟨?_, fun _ _ => rfl⟩
    rw [OpenPartialHomeomorph.restr_source' _ _ hopen, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_source, restrOpen_target, OpenPartialHomeomorph.restrOpen_source,
      OpenPartialHomeomorph.coe_restrOpen_symm]
    ext y
    simp only [_root_.Set.mem_inter_iff, _root_.Set.mem_preimage]
    tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.restrict ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.restrict

private theorem trans_cancel (F : X ≃ₜ X) (e e' : OpenPartialHomeomorph X H) :
    (F.toOpenPartialHomeomorph.trans e).symm.trans (F.toOpenPartialHomeomorph.trans e') =
      e.symm.trans e' := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc F.toOpenPartialHomeomorph.symm,
    ← Homeomorph.symm_toOpenPartialHomeomorph, ← Homeomorph.trans_toOpenPartialHomeomorph,
    Homeomorph.symm_trans_self]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.trans_cancel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.AtlasOn.trans_cancel target :: scope.openDecls } }

def transport (A : AtlasOn G U) (F : X ≃ₜ X) : AtlasOn G (F '' U) where
  charts := (fun e => F.symm.toOpenPartialHomeomorph.trans e) '' A.charts
  source_subset := by
    rintro _ ⟨e, he, rfl⟩ x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact ⟨F.symm x, A.source_subset e he hx.2, F.apply_symm_apply x⟩
  exists_mem_source := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, he, hxe⟩ := A.exists_mem_source x hx
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    simp [hxe]
  compatible := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    rw [trans_cancel]
    exact A.compatible e he e' he'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.transport ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.transport

theorem mem_charts_transport_iff {A : AtlasOn G U} {F : X ≃ₜ X}
    {e₀ : OpenPartialHomeomorph X H} :
    e₀ ∈ (A.transport F).charts ↔
      ∃ e ∈ A.charts, F.symm.toOpenPartialHomeomorph.trans e = e₀ :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.mem_charts_transport_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.mem_charts_transport_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.mem_charts_transport_iff ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.mem_charts_transport_iff

def union (A : AtlasOn G U) (B : AtlasOn G V)
    (h : ∀ e ∈ A.charts, ∀ e' ∈ B.charts, e.symm ≫ₕ e' ∈ G) : AtlasOn G (U ∪ V) where
  charts := A.charts ∪ B.charts
  source_subset e he := he.elim (fun he => (A.source_subset e he).trans _root_.Set.subset_union_left)
    fun he => (B.source_subset e he).trans _root_.Set.subset_union_right
  exists_mem_source x hx := hx.elim
    (fun hx => let ⟨e, he, hxe⟩ := A.exists_mem_source x hx; ⟨e, Or.inl he, hxe⟩)
    fun hx => let ⟨e, he, hxe⟩ := B.exists_mem_source x hx; ⟨e, Or.inr he, hxe⟩
  compatible e he e' he' := by
    rcases he with he | he <;> rcases he' with he' | he'
    · exact A.compatible e he e' he'
    · exact h e he e' he'
    · have hG := G.symm (h e' he' e he)
      rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] at hG
    · exact B.compatible e he e' he'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.union ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.union

@[instance_reducible] noncomputable def chartedSpace (A : AtlasOn G (_root_.Set.univ : Set X)) :
    ChartedSpace H X where
  atlas := A.charts
  chartAt x := (A.exists_mem_source x (_root_.Set.mem_univ x)).choose
  mem_chart_source x := (A.exists_mem_source x (_root_.Set.mem_univ x)).choose_spec.2
  chart_mem_atlas x := (A.exists_mem_source x (_root_.Set.mem_univ x)).choose_spec.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.chartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.chartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.chartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.chartedSpace

theorem hasGroupoid (A : AtlasOn G (_root_.Set.univ : Set X)) :
    letI := A.chartedSpace
    HasGroupoid X G := by
  let _ := A.chartedSpace
  exact ⟨fun he he' => A.compatible _ he _ he'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.hasGroupoid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.hasGroupoid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.hasGroupoid ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.hasGroupoid

def ofChartedSpace (G : StructureGroupoid H) [ChartedSpace H X] [HasGroupoid X G] :
    AtlasOn G (_root_.Set.univ : Set X) where
  charts := atlas H X
  source_subset _ _ := _root_.Set.subset_univ _
  exists_mem_source x _ := ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩
  compatible _ he _ he' := HasGroupoid.compatible he he'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.AtlasOn.ofChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.AtlasOn.ofChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.AtlasOn.ofChartedSpace ``Submission.DifferentialGeometry.Topology.Manifold.AtlasOn.ofChartedSpace

end AtlasOn

end DifferentialGeometry.Topology.Manifold
