/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonCircleParametrization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonGeneratedOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.WalkPathConcatenation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.SimpleGraph _root_.Submission.SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_fromLoops
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_fromLoops then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_fromLoops"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_fromLoops ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_fromLoops

omit [FiniteDimensional ℝ E] [Finite L.faces] in
open _root_.Classical in
theorem isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : ∀ ℓ : Path (vertexPoint (barycentricSubdivision L) v₀)
        (vertexPoint (barycentricSubdivision L) v₀),
      ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k)) :
    IsGeneratedByPolygon γ :=
  fun u p => exists_zpow_conjugate_homotopic_walkPath hconn γ hgen u p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow

open _root_.Classical in
theorem isOrientable_of_ambient_nullHomotopic_loop_generated_polygon
    (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : ∀ ℓ : Path (vertexPoint (barycentricSubdivision L) v₀)
        (vertexPoint (barycentricSubdivision L) v₀),
      ∃ k : ℤ, ℓ.Homotopic (loopZPow (walkPath γ) k))
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L :=
  isOrientable_of_ambient_nullHomotopic_generated_polygon hLK hK hL o hconn γ
    (isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow hconn γ hgen) hnull

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_loop_generated_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_loop_generated_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_loop_generated_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_loop_generated_polygon

open _root_.Classical in
theorem exists_isGeneratedByPolygon_of_isCombinatorialManifold_one
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ (v₀ : (barycentricSubdivision L).vertices)
      (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀),
      γ.IsCycle ∧ γ.toSubgraph.verts = Set.univ ∧ IsGeneratedByPolygon γ := by
  have hB : IsCombinatorialManifold 1 (barycentricSubdivision L) := hL.barycentricSubdivision
  have hBconn : IsConnected (barycentricSubdivision L).space :=
    (barycentricSubdivision_isSubdivision L).space_eq.symm ▸ hconn
  obtain ⟨v₀, γ, hcyc, hspan, hgen⟩ := exists_cycle_generating_loops hB hBconn
  exact ⟨v₀, γ, hcyc, hspan,
    isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow
      (edgeGraph_connected_of_isConnected_space _ hBconn).preconnected γ hgen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_of_isCombinatorialManifold_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_of_isCombinatorialManifold_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_of_isCombinatorialManifold_one ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_of_isCombinatorialManifold_one

end DifferentialGeometry.Topology.PiecewiseLinear
