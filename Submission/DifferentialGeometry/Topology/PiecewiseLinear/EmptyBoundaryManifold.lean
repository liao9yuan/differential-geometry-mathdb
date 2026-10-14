/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFaces

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsCombinatorialManifoldWithBoundary.isCombinatorialManifold_of_empty_boundary
    [d : DecidableEq E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hB : (boundaryComplex (n + 1) K).space = ∅) : IsCombinatorialManifold (n + 1) K := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  intro v hv
  rcases hK v hv with hS | hball
  · exact hS
  · have hvB : {v} ∈ (boundaryComplex (n + 1) K).faces := by
      refine ⟨hv, {v}, hv, Subset.rfl, by simp, ?_⟩
      simpa only [Finset.card_singleton, Nat.add_sub_cancel_right] using hball
    have hxB := (boundaryComplex (n + 1) K).subset_space hvB (Finset.mem_singleton_self v)
    exact (_root_.Set.notMem_empty v (hB ▸ hxB)).elim

run_cmd do
  let env ← Lean.getEnv
  match env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifold_of_empty_boundary with
  | true => throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifold_of_empty_boundary"
  | false => pure ()
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifold_of_empty_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isCombinatorialManifold_of_empty_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
