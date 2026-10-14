/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C A B : Set E} {a b : E}

theorem IsBridgeDisk.subset (h : IsBridgeDisk C A B a b) : A ⊆ C := by
  obtain ⟨q, hq, hBC, hA, -, -, -⟩ := h
  rw [← hA]
  exact (_root_.Set.image_mono (fun _ hx => hx.1)).trans (hq.image_eq.subset.trans hBC)

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.subset

theorem IsBridgeDisk.inter_frontier (h : IsBridgeDisk C A B a b) :
    A ∩ frontier C = {a, b} := by
  obtain ⟨q, hq, -, hA, hfr, hq0, hq1⟩ := h
  have hAB : A ⊆ B := by
    rw [← hA]
    exact (_root_.Set.image_mono (fun _ hx => hx.1)).trans hq.image_eq.subset
  calc
    A ∩ frontier C = A ∩ (B ∩ frontier C) := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hAB hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
    _ = q '' standardTriangleBase ∩ q '' standardTriangleSides := by rw [hfr, hA]
    _ = q '' (standardTriangleBase ∩ standardTriangleSides) :=
      (hq.bijOn.injOn.image_inter (fun _ hx => hx.1) (fun _ hx => hx.1)).symm
    _ = {a, b} := by rw [standardTriangleBase_inter_sides, _root_.Set.image_pair, hq0, hq1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_frontier

theorem IsBridgeDisk.sdiff_subset_interior (h : IsBridgeDisk C A B a b) :
    A \ {a, b} ⊆ interior C := by
  rintro x ⟨hxA, hxends⟩
  by_contra hxint
  exact hxends (h.inter_frontier.subset ⟨hxA, subset_closure (h.subset hxA), hxint⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.sdiff_subset_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.sdiff_subset_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.sdiff_subset_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.sdiff_subset_interior

theorem IsBridgeDisk.inter_boundary_subset (h : IsBridgeDisk C A B a b)
    {D : Set E} (hD : D ⊆ frontier C) : A ∩ D ⊆ {a, b} :=
  (_root_.Set.inter_subset_inter_right A hD).trans h.inter_frontier.subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_boundary_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_boundary_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_boundary_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.inter_boundary_subset

theorem IsBridgeDisk.exists_parametrization [FiniteDimensional ℝ E]
    (h : IsBridgeDisk C A B a b) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (_root_.Set.Icc 0 1) A ∧ γ 0 = a ∧ γ 1 = b := by
  obtain ⟨q, hq, -, hA, -, hq0, hq1⟩ := h
  let α := AffineMap.lineMap (k := ℝ) (![1, 0, 0] : Fin 3 → ℝ) ![0, 1, 0]
  have hne : (![1, 0, 0] : Fin 3 → ℝ) ≠ ![0, 1, 0] := by
    intro heq
    have h0 := congrFun heq 0
    norm_num at h0
  have hα : IsPLHomeomorphOn α (_root_.Set.Icc 0 1) standardTriangleBase := by
    rw [standardTriangleBase_eq_segment]
    exact isPLHomeomorphOn_lineMap_Icc_segment hne
  have hbase : IsPolyhedron standardTriangleBase := by
    rw [standardTriangleBase_eq_segment]
    exact (isPLBall_segment hne).isPolyhedron
  have hqbase := hq.restrict hbase (fun _ hx => hx.1)
  rw [hA] at hqbase
  refine ⟨q ∘ α, hα.trans hqbase, ?_, ?_⟩
  · simpa only [Function.comp_apply, α, AffineMap.lineMap_apply_zero] using hq0
  · simpa only [Function.comp_apply, α, AffineMap.lineMap_apply_one] using hq1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_parametrization ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_parametrization

end DifferentialGeometry.Topology.PiecewiseLinear
