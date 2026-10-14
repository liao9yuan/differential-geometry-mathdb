/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SurfaceRegion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsConeBase.isPLBall_of_apex_mem_frontier {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hM : IsCombinatorialManifoldWithBoundary (n + 1) (coneComplex hL))
    (hp : p ∈ frontier (coneComplex hL).space) : IsPLBall n L.space := by
  classical
  let _ : Finite (coneComplex hL).faces := (coneComplex_faces_finite hL (Set.toFinite
      L.faces)).to_subtype
  have hlink : SimplicialComplex.geometricLink (coneComplex hL) {p} = L :=
    Geometry.SimplicialComplex.ext (geometricLink_coneComplex_faces hL)
  have hpB : p ∈ (boundaryComplex (n + 1) (coneComplex hL)).space := by
    rwa [← frontier_space_eq_boundaryComplex_space_of_finrank hdim (coneComplex hL) hM]
  rw [← hlink]
  exact (isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision
    (coneComplex hL) (coneComplex hL) hM (IsSubdivision.refl _) (Or.inr (Or.inl rfl))).mpr hpB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_apex_mem_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_apex_mem_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_apex_mem_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_apex_mem_frontier

open _root_.Classical in
theorem IsConeBase.isPLBall_of_isPLSphere_frontier
    (hdim : Module.finrank ℝ E = 3) {p : E}
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsConeBase p L)
    (hreg : closure (interior (coneComplex hL).space) = (coneComplex hL).space)
    (hS : IsPLSphere 2 (frontier (coneComplex hL).space))
    (hp : p ∈ frontier (coneComplex hL).space) : IsPLBall 2 L.space := by
  classical
  let _ : Finite (coneComplex hL).faces := (coneComplex_faces_finite hL (Set.toFinite
      L.faces)).to_subtype
  exact hL.isPLBall_of_apex_mem_frontier hdim
    (isCombinatorialManifoldWithBoundary_of_isPLSphere_frontier (coneComplex hL) hdim hreg hS) hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsConeBase.isPLBall_of_isPLSphere_frontier

end DifferentialGeometry.Topology.PiecewiseLinear
