/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CocycleWalkLift
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonNeighborhoodOrientation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.SimpleGraph _root_.Submission.SimpleGraph

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_contractiblePolygon
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (s : Finset E) :
    Finite (faceStarComplex L s).faces := (faceStarComplex_faces_finite L s).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_contractiblePolygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_contractiblePolygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_contractiblePolygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_contractiblePolygon

open _root_.Classical in
theorem isOrientable_of_nullHomotopic_polygon
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    {v₀ : (barycentricSubdivision K).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk v₀ v₀)
    (hgen : ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (orientationCocycle hK o).walkMonodromy p = 0 ∨
        (orientationCocycle hK o).walkMonodromy p =
          (orientationCocycle hK o).walkMonodromy γ)
    (hnull : (walkPath γ).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K) v₀))) :
    IsOrientable n K :=
  isOrientable_of_polygon_walkMonodromy_eq_zero hK o hconn γ hgen
    ((orientationCocycle hK o).walkMonodromy_eq_zero_of_homotopic_refl γ hnull)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_nullHomotopic_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_nullHomotopic_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_nullHomotopic_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_nullHomotopic_polygon

open _root_.Classical in
theorem isOrientable_of_forall_nullHomotopic_walk
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Preconnected)
    (hnull : ∀ (u : (barycentricSubdivision K).vertices)
      (p : (SimplicialComplex.edgeGraph (barycentricSubdivision K)).Walk u u),
      (walkPath p).Homotopic (Path.refl (vertexPoint (barycentricSubdivision K) u))) :
    IsOrientable n K :=
  isOrientable_of_forall_walkMonodromy_eq_zero hK o hconn fun u p =>
    (orientationCocycle hK o).walkMonodromy_eq_zero_of_homotopic_refl p (hnull u p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_forall_nullHomotopic_walk then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_forall_nullHomotopic_walk"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_forall_nullHomotopic_walk ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_forall_nullHomotopic_walk

end DifferentialGeometry.Topology.PiecewiseLinear
