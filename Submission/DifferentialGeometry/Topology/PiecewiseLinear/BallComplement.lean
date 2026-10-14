/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPolyhedron.sdiff_interior_of_isPLBall {n : ℕ}
    {P D : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPolyhedron P)
    (hD : IsPLBall (n + 1) D) : IsPolyhedron (P \ interior D) := by
  have heq : P \ interior D = closure (P \ D) ∪ (P ∩ frontier D) := by
    apply Subset.antisymm
    · intro x hx
      by_cases hxD : x ∈ D
      · exact Or.inr ⟨hx.1, subset_closure hxD, hx.2⟩
      · exact Or.inl (subset_closure ⟨hx.1, hxD⟩)
    · refine _root_.Set.union_subset ?_ (fun _ hx => ⟨hx.1, hx.2.2⟩)
      exact closure_minimal (fun _ hx => ⟨hx.1, fun h => hx.2 (interior_subset h)⟩)
        (hP.isClosed.sdiff isOpen_interior)
  rw [heq]
  exact (hP.closure_sdiff hD.isPolyhedron).union (hP.inter hD.isPLSphere_frontier.isPolyhedron)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_interior_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_interior_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_interior_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedron.sdiff_interior_of_isPLBall

end DifferentialGeometry.Topology.PiecewiseLinear
