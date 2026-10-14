/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexPush
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplexCorner

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

theorem closure_frontier_convexHull_sdiff_convexHull_erase (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    {a : E} (ha : a ∈ T) :
    closure (frontier (convexHull ℝ (T : Set E)) \ convexHull ℝ (T.erase a : Set E)) =
      (simplexAvoiding T hT {T.erase a}).space := by
  have hins : _root_.Insert.insert a (T.erase a) = T := Finset.insert_erase ha
  have hTa : AffineIndependent ℝ ((↑) : (_root_.Insert.insert a (T.erase a) : Finset E) → E) := hins.symm ▸ hT
  have hspan' : affineSpan ℝ ((_root_.Insert.insert a (T.erase a) : Finset E) : Set E) = ⊤ := hins.symm ▸ hspan
  have h := closure_frontier_convexHull_sdiff_face (T.erase a) (Finset.notMem_erase a T) hTa hspan'
  rw [hins] at h
  rw [h, simplexAvoiding_singleton_space]
  apply _root_.Set.iUnion_congr
  intro v
  apply _root_.Set.iUnion_congr
  intro hv
  have hav : a ∈ T.erase v := Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hv).symm, ha⟩
  rw [Finset.erase_right_comm, Finset.insert_erase hav]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closure_frontier_convexHull_sdiff_convexHull_erase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closure_frontier_convexHull_sdiff_convexHull_erase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closure_frontier_convexHull_sdiff_convexHull_erase ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closure_frontier_convexHull_sdiff_convexHull_erase

theorem convexHull_erase_inter_closure_frontier_sdiff (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hspan : affineSpan ℝ (T : Set E) = ⊤)
    {a : E} (ha : a ∈ T) :
    convexHull ℝ (T.erase a : Set E) ∩
      closure (frontier (convexHull ℝ (T : Set E)) \ convexHull ℝ (T.erase a : Set E)) =
      (simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))).space
          := by
  rw [closure_frontier_convexHull_sdiff_convexHull_erase T hT hspan ha, _root_.Set.inter_comm]
  exact simplexAvoiding_space_inter_convexHull_erase T hT a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.convexHull_erase_inter_closure_frontier_sdiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.convexHull_erase_inter_closure_frontier_sdiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.convexHull_erase_inter_closure_frontier_sdiff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.convexHull_erase_inter_closure_frontier_sdiff

end DifferentialGeometry.Topology.PiecewiseLinear
