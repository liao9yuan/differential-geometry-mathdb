/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolytopeBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConvexCone
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLSphere_frontier_and_isPLBall_of_convex {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {C : Set E} (hC : Convex ℝ C)
    (hcompact : IsCompact C) (hinter : (interior C).Nonempty)
    (hfront : IsPolyhedron (frontier C)) :
    IsPLSphere n (frontier C) ∧ IsPLBall (n + 1) C := by
  classical
  obtain ⟨p, hp⟩ := hinter
  obtain ⟨L, hLfin, hLspace⟩ := hfront.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  let hpL := isConeBase_of_space_subset_frontier_convex hC hcompact.isClosed hp L hLspace.le
  let _ : Finite (coneComplex hpL).faces := (coneComplex_faces_finite hpL hLfin).to_subtype
  have hcone : (coneComplex hpL).space = C :=
    coneComplex_space_eq_of_convex hC hcompact (interior_subset hp) hpL hLspace
  have hlink : SimplicialComplex.geometricLink (coneComplex hpL) {p} = L := by
    apply Geometry.SimplicialComplex.ext
    exact geometricLink_coneComplex_faces hpL
  have hL : IsPLSphere n L.space := by
    rw [← hlink]
    exact isPLSphere_geometricLink_of_mem_nhds hn (coneComplex hpL) (Or.inr (Or.inl rfl))
      (hcone.symm ▸ mem_interior_iff_mem_nhds.mp hp)
  exact ⟨hLspace ▸ hL, hcone ▸ hpL.isPLBall_of_isPLSphere hL⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_frontier_and_isPLBall_of_convex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_frontier_and_isPLBall_of_convex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_frontier_and_isPLBall_of_convex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLSphere_frontier_and_isPLBall_of_convex

theorem IsHPolytope.isPLSphere_frontier {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) {C : Set E} (hC : IsHPolytope C)
    (hinter : (interior C).Nonempty) : IsPLSphere n (frontier C) :=
  (isPLSphere_frontier_and_isPLBall_of_convex hn hC.convex hC.isCompact hinter
    hC.isPolyhedron_frontier).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLSphere_frontier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLSphere_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLSphere_frontier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLSphere_frontier

theorem IsHPolytope.isPLBall {C : Set E} (hC : IsHPolytope C)
    (hinter : (interior C).Nonempty) : IsPLBall (Module.finrank ℝ E) C := by
  classical
  cases hn : Module.finrank ℝ E with
  | zero =>
    let _ : Subsingleton E := (Module.finrank_zero_iff (R := ℝ) (M := E)).mp hn
    obtain ⟨p, hp⟩ := hinter
    have heq : C = {p} := Subset.antisymm (fun _ _ => Subsingleton.elim _ _)
      (singleton_subset_iff.mpr (interior_subset hp))
    rw [heq]
    simpa only [Finset.coe_singleton, convexHull_singleton] using
      isPLBall_convexHull_of_affineIndependent ({p} : Finset E)
        (affineIndependent_of_subsingleton ℝ _) (by simp : ({p} : Finset E).card = 0 + 1)
  | succ n =>
    exact (isPLSphere_frontier_and_isPLBall_of_convex hn hC.convex hC.isCompact hinter
      hC.isPolyhedron_frontier).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsHPolytope.isPLBall

end DifferentialGeometry.Topology.PiecewiseLinear
