/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceRegion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphereCellPush
import Submission.DifferentialGeometry.Topology.ConvexFrontier
import Submission.DifferentialGeometry.Topology.RegularClosed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem frontier_closure_sdiff_eq_of_isPLSphere_frontier
    {P C : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPolyhedron P)
    (hreg : closure (interior P) = P) (hS : IsPLSphere 2 (frontier P))
    (hC : IsPLBall 3 C) (hCP : C ⊆ P) (hpatch : IsPLBall 2 (frontier P ∩ C)) :
    frontier (closure (P \ C)) = closure (frontier P \ C) ∪ closure (frontier C \ frontier P) := by
  classical
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  obtain ⟨K, hKfin, hKspace⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    isCombinatorialManifoldWithBoundary_of_isPLSphere_frontier K (by simp)
    (by rwa [hKspace]) (by rwa [hKspace])
  have hKfront : frontier K.space = (boundaryComplex 3 K).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (by simp) K hK
  have hCK : C ⊆ K.space := hCP.trans hKspace.symm.subset
  have hpatchK : IsPLBall 2 (C ∩ (boundaryComplex 3 K).space) := by
    rw [← hKfront, hKspace, _root_.Set.inter_comm]
    exact hpatch
  obtain ⟨R, hRfin, hR, hRspace⟩ := hK.exists_isCombinatorialManifoldWithBoundary_closure_sdiff hC
      hCK hpatchK
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨A, hAfin, hAspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAspace.symm ▸ hC
  have hAfront : frontier A.space = (boundaryComplex 3 A).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (by simp) A
        hA.isCombinatorialManifoldWithBoundary
  have hRfront : frontier R.space = (boundaryComplex 3 R).space :=
    frontier_space_eq_boundaryComplex_space_of_finrank (by simp) R hR
  have hformula := boundaryComplex_space_of_closure_sdiff K A R hK
    hA.isCombinatorialManifoldWithBoundary (hAspace.subset.trans hCK) hR (by rwa [hAspace])
  rw [← hRfront, ← hKfront, ← hAfront, hRspace, hKspace, hAspace] at hformula
  exact hformula

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.frontier_closure_sdiff_eq_of_isPLSphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.frontier_closure_sdiff_eq_of_isPLSphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.frontier_closure_sdiff_eq_of_isPLSphere_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.frontier_closure_sdiff_eq_of_isPLSphere_frontier

theorem exists_isPLHomeomorphOn_frontier_closure_sdiff_of_convex (I : SchoenfliesInput)
    {P C W : Set (EuclideanSpace ℝ (Fin 3))} (hP : IsPolyhedron P)
    (hreg : closure (interior P) = P) (hS : IsPLSphere 2 (frontier P))
    (hC : IsPLBall 3 C) (hconv : Convex ℝ C) (hCP : C ⊆ P)
    (hpatch : IsPLBall 2 (frontier P ∩ C))
    (hW : IsOpen W) (hWconv : Convex ℝ W) (hSW : frontier P ⊆ W) :
    ∃ H : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn H _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn H id Wᶜ ∧ _root_.Set.EqOn H id (closure (frontier P \ C)) ∧
      H '' frontier P = frontier (closure (P \ C)) := by
  have hPW : P ⊆ W := Topology.subset_of_isCompact_of_frontier_subset_open_convex
    hP.isCompact hW hWconv (hS.nonempty.mono hSW) hSW
  have hpatchBd : frontier P ∩ C ⊆ frontier C := by
    rintro x ⟨hxP, hxC⟩
    exact ⟨subset_closure hxC, fun hint => hxP.2 (interior_mono hCP hint)⟩
  obtain ⟨H, hH, hfix, hfixS, himage⟩ := exists_isPLHomeomorphOn_sphere_surgery_of_convex
    I hS hC hconv hpatch hpatchBd hW (hCP.trans hPW)
  rw [← frontier_closure_sdiff_eq_of_isPLSphere_frontier hP hreg hS hC hCP hpatch] at himage
  exact ⟨H, hH, hfix, hfixS, himage⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_frontier_closure_sdiff_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_frontier_closure_sdiff_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_frontier_closure_sdiff_of_convex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_frontier_closure_sdiff_of_convex

end DifferentialGeometry.Topology.PiecewiseLinear
