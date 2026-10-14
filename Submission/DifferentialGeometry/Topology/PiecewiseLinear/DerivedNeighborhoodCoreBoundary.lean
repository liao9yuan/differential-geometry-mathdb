/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) (hLK : L.faces ⊆ K.faces) :
    Disjoint L.space (boundaryComplex (n + 1) (derivedNeighborhood K L)).space := by
  classical
  have : Finite (derivedNeighborhood K L).faces :=
    (derivedNeighborhood_faces_finite K L).to_subtype
  apply disjoint_left.mpr
  intro x hxL hxB
  have hnhds := derivedNeighborhood_mem_nhdsWithin hLK hxL
  have hxN : x ∈ (derivedNeighborhood K L).space :=
    mem_of_mem_nhdsWithin (space_mono_of_faces_subset hLK hxL) hnhds
  have hx := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K
    (derivedNeighborhood K L) hK.isCombinatorialManifoldWithBoundary
    (hK.isCombinatorialManifoldWithBoundary.derivedNeighborhood L)
    (derivedNeighborhood_space_subset K L) hxN hnhds).mp hxB
  rw [Geometry.SimplicialComplex.space, hK.boundaryComplex_faces_eq_empty K] at hx
  simp at hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifold.disjoint_derivedNeighborhood_boundary

end DifferentialGeometry.Topology.PiecewiseLinear
