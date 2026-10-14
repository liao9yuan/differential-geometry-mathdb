/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.AmbientPolygonOrientation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialWalkHomotopy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.WalkMonodromyHomotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.SimpleGraph _root_.Submission.SimpleGraph

section Simplicial

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Geometry.SimplicialComplex ℝ F}

open _root_.Classical in
theorem SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_zpow
    (ε : SimplicialBoolCocycle M) {v₀ u : M.vertices}
    (γ : (SimplicialComplex.edgeGraph M).Walk v₀ v₀)
    (p : (SimplicialComplex.edgeGraph M).Walk u u)
    (q : (SimplicialComplex.edgeGraph M).Walk u v₀) (k : ℤ)
    (hp : SimplicialHomotopic M p (q.append ((closedWalkZPow γ k).append q.reverse))) :
    ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [ε.walkMonodromy_eq_of_simplicialHomotopic hp, ε.walkMonodromy_conjugate,
    ε.walkMonodromy_closedWalkZPow]
  rcases hx ((k : ZMod 2)) with hk | hk
  · exact Or.inl (by rw [hk, _root_.MulZeroClass.zero_mul])
  · exact Or.inr (by rw [hk, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_zpow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_zpow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_zpow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_zpow

open _root_.Classical in
theorem SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow
    (ε : SimplicialBoolCocycle M) {v₀ u : M.vertices}
    (γ : (SimplicialComplex.edgeGraph M).Walk v₀ v₀)
    (p : (SimplicialComplex.edgeGraph M).Walk u u)
    (q : (SimplicialComplex.edgeGraph M).Walk u v₀) (k : ℕ)
    (hp : SimplicialHomotopic M p (q.append ((closedWalkPow γ k).append q.reverse))) :
    ε.walkMonodromy p = 0 ∨ ε.walkMonodromy p = ε.walkMonodromy γ := by
  have hx : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rw [ε.walkMonodromy_eq_of_simplicialHomotopic hp, ε.walkMonodromy_conjugate,
    ε.walkMonodromy_closedWalkPow]
  rcases hx (k : ZMod 2) with hk | hk
  · exact Or.inl (by rw [hk, _root_.MulZeroClass.zero_mul])
  · exact Or.inr (by rw [hk, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_pow

end Simplicial

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_polygonGenerated
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_polygonGenerated then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_polygonGenerated"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_polygonGenerated ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_polygonGenerated

open _root_.Classical in
def IsGeneratedByPolygon {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀) : Prop :=
  ∀ (u : (barycentricSubdivision L).vertices)
    (p : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u u),
    ∃ (q : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u v₀) (k : ℤ),
      (walkPath p).Homotopic (walkPath (q.append ((closedWalkZPow γ k).append q.reverse)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGeneratedByPolygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGeneratedByPolygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGeneratedByPolygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGeneratedByPolygon

open _root_.Classical in
def IsSimpliciallyGeneratedByPolygon {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀) : Prop :=
  ∀ (u : (barycentricSubdivision L).vertices)
    (p : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u u),
    ∃ (q : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk u v₀) (k : ℤ),
      SimplicialHomotopic (barycentricSubdivision L) p
        (q.append ((closedWalkZPow γ k).append q.reverse))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSimpliciallyGeneratedByPolygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSimpliciallyGeneratedByPolygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSimpliciallyGeneratedByPolygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSimpliciallyGeneratedByPolygon

open _root_.Classical in
theorem isOrientable_of_ambient_nullHomotopic_generated_polygon (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : IsGeneratedByPolygon γ)
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L := by
  refine isOrientable_of_ambient_nullHomotopic_polygon hLK hK hL o hconn γ (fun u p => ?_) hnull
  obtain ⟨q, k, hq⟩ := hgen u p
  exact SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_homotopic_conjugate_zpow _ γ p q k hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_generated_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_generated_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_generated_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_generated_polygon

open _root_.Classical in
theorem isOrientable_of_ambient_nullHomotopic_simplicially_generated_polygon
    (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (hconn : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Preconnected)
    {v₀ : (barycentricSubdivision L).vertices}
    (γ : (SimplicialComplex.edgeGraph (barycentricSubdivision L)).Walk v₀ v₀)
    (hgen : IsSimpliciallyGeneratedByPolygon γ)
    (hnull : (walkPath (γ.map (edgeGraphHom (barycentricSubdivision_faces_subset hLK)))).Homotopic
      (Path.refl (vertexPoint (barycentricSubdivision K)
        (edgeGraphHom (barycentricSubdivision_faces_subset hLK) v₀)))) :
    IsOrientable n L := by
  refine isOrientable_of_ambient_nullHomotopic_polygon hLK hK hL o hconn γ (fun u p => ?_) hnull
  obtain ⟨q, k, hq⟩ := hgen u p
  exact SimplicialBoolCocycle.walkMonodromy_eq_zero_or_eq_of_simplicialHomotopic_conjugate_zpow
    _ γ p q k hq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_simplicially_generated_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_simplicially_generated_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_simplicially_generated_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_of_ambient_nullHomotopic_simplicially_generated_polygon

end DifferentialGeometry.Topology.PiecewiseLinear
