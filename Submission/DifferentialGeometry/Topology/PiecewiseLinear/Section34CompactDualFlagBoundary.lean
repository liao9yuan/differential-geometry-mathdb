/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundedLabelUnion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualArcBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualOuterBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualPatchBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualSplitBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem compactDualCutBoundary_markedPoint_eq_empty
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (p : Section34CompactMarkIndex K K) :
    compactDualCutBoundary M K hKM (.markedPoint p) = ∅ := by
  obtain ⟨P, r, u, -, -, -, hbd⟩ := isPLCellOn_compactDualMarkedPoint M K hKM p
  rw [hbd, stdSimplexBoundary_zero, _root_.Set.image_empty, _root_.Set.image_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_markedPoint_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_markedPoint_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_markedPoint_eq_empty ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_markedPoint_eq_empty

theorem compactDualCutBoundary_eq_iUnion_step
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space)
    (l : Section34CompactLabelOf K K) :
    compactDualCutBoundary M K hKM l =
      ⋃ (m : Section34CompactLabelOf K K) (_ : Section34CompactCutStep m l),
        compactDualCutCell M K hKM m := by
  rw [iUnion_section34BoundedLabel]
  cases l with
  | vertexBall w =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_vertexBall_eq_union M K hM hK hKM hint w
  | tetraBall t =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_tetraBall_eq_union M K hKM hM t
  | splitDisk e =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_splitDisk_eq_union M K hM hK hKM hint e
  | faceDisk s =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_faceDisk_eq_iUnion_faceArc M K hKM s
  | patch x =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_patch_eq_union M K hKM x
  | faceArc a =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_faceArc_eq_iUnion_markedPoint M K hKM a
  | edgeArc i =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_edgeArc_eq_iUnion_markedPoint M K hKM i
  | markedPoint p =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_markedPoint_eq_empty M K hKM p
  | outerFace o =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_outerFace_eq_union M K hM hK hKM hint o
  | outerArc q =>
    simpa only [Section34CompactCutStep, _root_.Set.iUnion_false, _root_.Set.iUnion_empty, _root_.Set.empty_union, _root_.Set.union_empty]
      using compactDualCutBoundary_outerArc_eq_union M K hM hK hKM hint q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_eq_iUnion_step then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_eq_iUnion_step"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_eq_iUnion_step ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compactDualCutBoundary_eq_iUnion_step

end DifferentialGeometry.Topology.PiecewiseLinear
