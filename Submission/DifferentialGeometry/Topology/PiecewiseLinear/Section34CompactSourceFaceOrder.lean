/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBoundaryIncidence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceFacets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

namespace CompactSourceFaceProbe

private theorem cutStep_iff_source_subset_outerFace
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (o : Section34CompactOuterVertexIndex K K')
    (hd : section34BoundedDim m = 1) :
    Section34CompactCutStep m (.outerFace o) ↔ src m ⊆ src (.outerFace o) := by
  cases m with
  | faceArc a => exact (hcut.faceArc_subset_outerFace_iff a o).symm
  | edgeArc i => exact ⟨False.elim, hcut.not_edgeArc_subset_outerFace i o⟩
  | outerArc q => exact (hcut.outerArc_subset_outerFace_iff q o).symm
  | _ => simp [section34BoundedDim] at hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cutStep_iff_source_subset_outerFace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cutStep_iff_source_subset_outerFace target :: scope.openDecls } }

private theorem cutStep_iff_source_subset_outerArc
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m : Section34CompactLabelOf K K'} (q : Section34CompactOuterEdgeIndex K K')
    (hd : section34BoundedDim m = 0) :
    Section34CompactCutStep m (.outerArc q) ↔ src m ⊆ src (.outerArc q) := by
  cases m with
  | markedPoint p => exact (hcut.markedPoint_subset_outerArc_iff p q).symm
  | _ => simp [section34BoundedDim] at hd

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cutStep_iff_source_subset_outerArc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cutStep_iff_source_subset_outerArc target :: scope.openDecls } }

theorem cut_step_iff_codimension_one_source_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'}
    (hd : section34BoundedDim l = section34BoundedDim m + 1) :
    Section34CompactCutStep m l ↔ src m ⊆ src l := by
  cases l with
  | vertexBall w =>
    exact hcut.cutStep_iff_source_subset_vertexBall w
      (by change 3 = section34BoundedDim m + 1 at hd; omega)
  | tetraBall t =>
    exact hcut.cutStep_iff_source_subset_tetraBall t
      (by change 3 = section34BoundedDim m + 1 at hd; omega)
  | splitDisk e =>
    exact hcut.cutStep_iff_source_subset_splitDisk e
      (by change 2 = section34BoundedDim m + 1 at hd; omega)
  | faceDisk s =>
    exact hcut.cutStep_iff_source_subset_faceDisk s
      (by change 2 = section34BoundedDim m + 1 at hd; omega)
  | patch x =>
    exact hcut.cutStep_iff_source_subset_patch x
      (by change 2 = section34BoundedDim m + 1 at hd; omega)
  | outerFace o =>
    exact cutStep_iff_source_subset_outerFace hcut o
      (by change 2 = section34BoundedDim m + 1 at hd; omega)
  | faceArc a =>
    exact hcut.cutStep_iff_source_subset_faceArc a
      (by change 1 = section34BoundedDim m + 1 at hd; omega)
  | edgeArc i =>
    exact hcut.cutStep_iff_source_subset_edgeArc i
      (by change 1 = section34BoundedDim m + 1 at hd; omega)
  | outerArc q =>
    exact cutStep_iff_source_subset_outerArc hcut q
      (by change 1 = section34BoundedDim m + 1 at hd; omega)
  | markedPoint p => simp [section34BoundedDim] at hd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_step_iff_codimension_one_source_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_step_iff_codimension_one_source_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_step_iff_codimension_one_source_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_step_iff_codimension_one_source_subset

theorem cut_order_of_source_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : src m ⊆ src l) :
    Section34CompactCutLe m l := by
  have aux : ∀ d, ∀ l : Section34CompactLabelOf K K',
      section34BoundedDim l = d → ∀ m, src m ⊆ src l → Section34CompactCutLe m l := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro l hld m hml
        by_cases h : m = l
        · subst m
          exact Relation.ReflTransGen.refl
        obtain ⟨k, hkd, hmk, hkl⟩ := exists_facet_above_of_source_subset hcut hml h
        have hklt : section34BoundedDim k < d := by omega
        have hstep : Section34CompactCutStep k l :=
          (cut_step_iff_codimension_one_source_subset hcut (by omega)).2 hkl
        exact Relation.ReflTransGen.tail (ih _ hklt k rfl m hmk) hstep
  exact aux _ l rfl m hml

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_order_of_source_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_order_of_source_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_order_of_source_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.cut_order_of_source_subset

theorem source_subset_of_cut_order
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    {m l : Section34CompactLabelOf K K'} (hml : Section34CompactCutLe m l) :
    src m ⊆ src l := by
  induction hml using Relation.ReflTransGen.head_induction_on with
  | refl => exact subset_rfl
  | @head b c hab hbc ih =>
      exact ((cut_step_iff_codimension_one_source_subset hcut
        (Section34CompactCutStep.dim_succ hab)).1 hab).trans ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.source_subset_of_cut_order then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.source_subset_of_cut_order"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.source_subset_of_cut_order ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactSourceFaceProbe.source_subset_of_cut_order

end CompactSourceFaceProbe

theorem compactSourceFace_iff_cutLe (hcut : Section34CompactCutFrame C K K' src srcBd) :
    ∀ l m : Section34CompactLabelOf K K', src m ⊆ src l ↔ Section34CompactCutLe m l := by
  intro l m
  exact ⟨CompactSourceFaceProbe.cut_order_of_source_subset hcut,
    CompactSourceFaceProbe.source_subset_of_cut_order hcut⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compactSourceFace_iff_cutLe then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compactSourceFace_iff_cutLe"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compactSourceFace_iff_cutLe ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compactSourceFace_iff_cutLe

end DifferentialGeometry.Topology.PiecewiseLinear
