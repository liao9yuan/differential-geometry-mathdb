/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnIntrinsicInterior
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualTraces
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterRecognition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchRecognition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLCellOn_compactDualCutCell
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hint : K.space ⊆ interior M.space)
    (l : Section34CompactLabelOf K K) :
    IsPLCellOn (section34BoundedDim l) (compactDualCutCell M K hKM l)
      (compactDualCutBoundary M K hKM l) := by
  cases l with
  | vertexBall w => exact isPLCellOn_compactDualVertexBall M K hKM hM w
  | tetraBall t => exact isPLCellOn_compactDualTetraBall M K hKM t
  | splitDisk e => exact isPLCellOn_compactDualSplitDisk M K hKM hM e
  | faceDisk s => exact isPLCellOn_compactDualFaceDisk M K hKM s
  | patch x =>
    exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.patch x)
      (isPLBall_compactDualCutCell_patch M K hKM x)
  | faceArc a => exact isPLCellOn_compactDualFaceArc M K hKM a
  | edgeArc i => exact isPLCellOn_compactDualEdgeArc M K hKM i
  | markedPoint p => exact isPLCellOn_compactDualMarkedPoint M K hKM p
  | outerFace o =>
    exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.outerFace o)
      (isPLBall_compactDualCutCell_outerFace M K hM hK hKM hint o)
  | outerArc q =>
    exact isPLCellOn_compactDualCutCell_of_isPLBall M K hKM (.outerArc q)
      (isPLBall_compactDualCutCell_outerArc M K hM hK hKM hint q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualCutCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualCutCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualCutCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLCellOn_compactDualCutCell

end DifferentialGeometry.Topology.PiecewiseLinear
