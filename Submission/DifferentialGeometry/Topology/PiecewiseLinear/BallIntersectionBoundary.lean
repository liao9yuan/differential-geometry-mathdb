/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBallTransport
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.subset_boundaryComplex_of_subset_inter_of_isPLBall
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (A B : Geometry.SimplicialComplex ℝ E) [Finite A.faces] [Finite B.faces]
    (hA : IsPLBall (n + 1) A.space) (hB : IsPLBall (n + 1) B.space)
    (hAK : A.space ⊆ K.space) (hBK : B.space ⊆ K.space)
    (hinter : A.space ∩ B.space ⊆ (boundaryComplex (n + 1) B).space)
    {D : Set E} (hD : IsPLBall n D) (hDAB : D ⊆ A.space ∩ B.space) :
    D ⊆ (boundaryComplex (n + 1) A).space := by
  let _ : DecidableEq E := Classical.decEq _
  obtain ⟨L, hLfin, hL, hLB, hmeet, _⟩ := exists_isPLBall_subset_inter_boundaryComplex B hB hD
    (hDAB.trans hinter)
  let _ : Finite L.faces := hLfin.to_subtype
  have hDL : D ⊆ L.space := hmeet.symm.subset.trans _root_.Set.inter_subset_left
  have hAL : A.space ∩ L.space = D := by
    apply Subset.antisymm
    · rintro x ⟨hxA, hxL⟩
      exact hmeet ▸ ⟨hxL, hinter ⟨hxA, hLB hxL⟩⟩
    · intro x hx
      exact ⟨(hDAB hx).1, hDL hx⟩
  have hI : IsPLBall n (A.space ∩ L.space) := hAL.symm ▸ hD
  have h := hK.inter_subset_boundaryComplex_of_isPLBall A hA hAK hL (hLB.trans hBK) hI
  rwa [hAL] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.subset_boundaryComplex_of_subset_inter_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.subset_boundaryComplex_of_subset_inter_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.subset_boundaryComplex_of_subset_inter_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.subset_boundaryComplex_of_subset_inter_of_isPLBall

end DifferentialGeometry.Topology.PiecewiseLinear
