/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem boundaryComplex_space_of_closure_sdiff_of_boundary_subset {n : ℕ}
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hRspace : R.space = closure (K.space \ A.space))
    (hbd : (boundaryComplex (n + 1) K).space ⊆ A.space) :
    (boundaryComplex (n + 1) R).space = R.space ∩ A.space := by
  apply Subset.antisymm
  · have heq := boundaryComplex_space_of_closure_sdiff K A R hK hA hAK hR hRspace
    rw [sdiff_eq_empty.mpr hbd, closure_empty, _root_.Set.empty_union] at heq
    refine _root_.Set.subset_inter (boundaryComplex_space_subset (n + 1) R) ?_
    rw [heq]
    exact closure_minimal (sdiff_subset.trans (boundaryComplex_space_subset (n + 1) A))
      (isPolyhedron_space A).isClosed
  · rw [_root_.Set.inter_comm]
    exact inter_space_complement_subset_boundaryComplex K A R hK hA hAK hR hRspace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_closure_sdiff_of_boundary_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_closure_sdiff_of_boundary_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_closure_sdiff_of_boundary_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_space_of_closure_sdiff_of_boundary_subset

end DifferentialGeometry.Topology.PiecewiseLinear
