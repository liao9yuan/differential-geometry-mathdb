/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open _root_.Classical in
theorem compact_vertex_split_incidence
    {M K : Geometry.SimplicialComplex ℝ E3} (hKM : K.faces ⊆ M.faces)
    (w : Section34CompactVertexIndex K K) (e : Section34CompactEdgeIndex K K)
    {v : E3} (hw : w.1 = {v})
    (hinter : ((graphDualCell M (restrict K (section34CompactGraphSkeleton K)) v).space ∩
      (splittingDisk M e.1 (hKM e.2.1)).space).Nonempty) :
    w.1 ⊆ e.1 := by
  have hv : {v} ∈ M.faces := hw ▸ hKM w.2.1
  rw [hw, Finset.singleton_subset_iff]
  exact mem_of_graphDualCell_inter_splittingDisk_nonempty M _ hv (hKM e.2.1) hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compact_vertex_split_incidence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compact_vertex_split_incidence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compact_vertex_split_incidence ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compact_vertex_split_incidence

theorem compact_face_disk_subset_residual_ball
    {K : Geometry.SimplicialComplex ℝ E3} {N : Set E3}
    (s : Section34CompactSimplexIndex K 3) (t : Section34CompactSimplexIndex K 4)
    (hst : Section34Incident s.1 t.1) :
    closure (convexHull ℝ (s.1 : Set E3) \ N) ⊆
      closure (convexHull ℝ (t.1 : Set E3) \ N) := by
  apply closure_mono
  exact _root_.Set.sdiff_subset_sdiff_left (convexHull_min hst (convex_convexHull ℝ _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.compact_face_disk_subset_residual_ball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.compact_face_disk_subset_residual_ball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.compact_face_disk_subset_residual_ball ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.compact_face_disk_subset_residual_ball

end DifferentialGeometry.Topology.PiecewiseLinear
