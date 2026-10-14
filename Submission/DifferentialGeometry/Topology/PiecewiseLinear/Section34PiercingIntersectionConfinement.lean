/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.NhdsWithin

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology _root_.Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_isOpen_of_mem_nhdsWithin
    {X : Type*} [TopologicalSpace X] {C A W : Set X}
    (hW : ∀ x ∈ C, W ∈ 𝓝[A] x) :
    ∃ V : Set X, IsOpen V ∧ C ⊆ V ∧ V ∩ A ⊆ W := by
  choose V hV hCV hVW using fun x : C => mem_nhdsWithin.mp (hW x x.2)
  refine ⟨⋃ x : C, V x, isOpen_iUnion hV, ?_, ?_⟩
  · exact fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hCV ⟨x, hx⟩⟩
  · rintro x ⟨hxV, hxA⟩
    obtain ⟨y, hy⟩ := mem_iUnion.mp hxV
    exact hVW y ⟨hy, hxA⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_of_mem_nhdsWithin
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.exists_isOpen_of_mem_nhdsWithin target :: scope.openDecls } }

theorem exists_intersection_confinement_of_compact
    {X : Type*} [MetricSpace X] {A B Wa Wb : Set X}
    (hA : IsCompact A) (hB : IsCompact B)
    (hWa : ∀ x ∈ A ∩ B, Wa ∈ 𝓝[A] x)
    (hWb : ∀ x ∈ A ∩ B, Wb ∈ 𝓝[B] x) :
    ∃ (Va Vb : Set X) (δ : ℝ), IsOpen Va ∧ IsOpen Vb ∧ A ∩ B ⊆ Va ∩ Vb ∧
      Va ∩ A ⊆ Wa ∧ Vb ∩ B ⊆ Wb ∧ 0 < δ ∧
      ∀ f : X → X, (∀ x ∈ A, _root_.Dist.dist (f x) x < δ) →
        f '' A ∩ B ⊆ f '' (Va ∩ A) ∩ Vb := by
  obtain ⟨Va, hVa, htraceVa, hVaWa⟩ := exists_isOpen_of_mem_nhdsWithin hWa
  obtain ⟨Vb, hVb, htraceVb, hVbWb⟩ := exists_isOpen_of_mem_nhdsWithin hWb
  have ha : Disjoint (A \ Va) B := Set.disjoint_left.mpr fun x hxA hxB =>
    hxA.2 (htraceVa ⟨hxA.1, hxB⟩)
  have hb : Disjoint A (B \ Vb) := Set.disjoint_left.mpr fun x hxA hxB =>
    hxB.2 (htraceVb ⟨hxA, hxB.1⟩)
  obtain ⟨a, haPos, haSep⟩ := ha.exists_cthickenings (hA.diff hVa) hB.isClosed
  obtain ⟨b, hbPos, hbSep⟩ := hb.exists_cthickenings hA (hB.diff hVb).isClosed
  refine ⟨Va, Vb, _root_.Min.min a b, hVa, hVb, _root_.Set.subset_inter htraceVa htraceVb, hVaWa, hVbWb,
    lt_min haPos hbPos, ?_⟩
  intro f hf y hy
  obtain ⟨x, hxA, rfl⟩ := hy.1
  have hfxa : _root_.Dist.dist (f x) x ≤ a := (hf x hxA).le.trans (min_le_left _ _)
  have hfxb : _root_.Dist.dist (f x) x ≤ b := (hf x hxA).le.trans (min_le_right _ _)
  have hxVa : x ∈ Va := by
    by_contra hxVa
    exact Set.disjoint_left.mp haSep
      (_root_.Metric.mem_cthickening_of_dist_le (f x) x a (A \ Va) ⟨hxA, hxVa⟩ hfxa)
      (_root_.Metric.self_subset_cthickening B hy.2)
  refine ⟨⟨x, ⟨hxVa, hxA⟩, rfl⟩, ?_⟩
  by_contra hfxVb
  exact Set.disjoint_left.mp hbSep
    (_root_.Metric.mem_cthickening_of_dist_le (f x) x b A hxA hfxb)
    (_root_.Metric.self_subset_cthickening (B \ Vb) ⟨hy.2, hfxVb⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_intersection_confinement_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_intersection_confinement_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_intersection_confinement_of_compact ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_intersection_confinement_of_compact

end DifferentialGeometry.Topology.PiecewiseLinear
