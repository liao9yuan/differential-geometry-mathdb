/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Homotopy.DeformationRetractLoopPower
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodHomology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodLoop
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCylinder
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonGeneratedFromLoops
import Submission.DifferentialGeometry.Topology.SimplicialComplex.GeometricConnectivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.SimpleGraph _root_.Submission.SimpleGraph
open _root_.Submission.DifferentialGeometry.Topology.Homotopy

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K P : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite P.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_derivedNeighborhoodPolygon
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_derivedNeighborhoodPolygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_derivedNeighborhoodPolygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_derivedNeighborhoodPolygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.finite_faceStarComplex_faces_derivedNeighborhoodPolygon

omit [FiniteDimensional ℝ E] [Finite K.faces] [Finite P.faces] in
open _root_.Classical in
theorem secondDerived_faces_subset_derivedNeighborhood (hPK : P.faces ⊆ K.faces) :
    (secondDerived P).faces ⊆ (derivedNeighborhood K P).faces := by
  rintro u ⟨D, hD, hne, rfl⟩
  exact ⟨D, hD.of_le (barycentricSubdivision_faces_subset hPK), hne,
    fun e he => exists_mem_image_centroid_of_mem_barycentricSubdivision (hD.mem_faces he), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset_derivedNeighborhood

open _root_.Classical in
def derivedNeighborhoodSubcomplexHomeomorph (hPK : P.faces ⊆ K.faces) :
    derivedNeighborhoodSubcomplex K P ≃ₜ P.space where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, subcomplex_space_subset_derivedNeighborhood hPK x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplexHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplexHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplexHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplexHomeomorph

omit [FiniteDimensional ℝ E] [Finite P.faces] in
open _root_.Classical in
theorem joinedIn_derivedNeighborhood_subcomplexBarycentricProjection {x : E}
    (hx : x ∈ (derivedNeighborhood K P).space) :
    JoinedIn (derivedNeighborhood K P).space x
      (subcomplexBarycentricProjection (barycentricSubdivision K)
        (barycentricSubdivision P) x) := by
  have hcont : Continuous fun t : unitInterval =>
      subcomplexBarycentricHomotopy (barycentricSubdivision K) (barycentricSubdivision P) t x :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  refine ⟨⟨⟨_, hcont⟩, ?_, ?_⟩,
    fun t => subcomplexBarycentricHomotopy_mem_derivedNeighborhood hx t⟩
  · simp [subcomplexBarycentricHomotopy]
  · simp [subcomplexBarycentricHomotopy]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.joinedIn_derivedNeighborhood_subcomplexBarycentricProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.joinedIn_derivedNeighborhood_subcomplexBarycentricProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.joinedIn_derivedNeighborhood_subcomplexBarycentricProjection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.joinedIn_derivedNeighborhood_subcomplexBarycentricProjection

omit [FiniteDimensional ℝ E] in
open _root_.Classical in
theorem isPathConnected_derivedNeighborhood_space (hPK : P.faces ⊆ K.faces)
    (hconn : IsConnected P.space) : IsPathConnected (derivedNeighborhood K P).space := by
  obtain ⟨x₀, hx₀, hjoin⟩ := SimplicialComplex.isPathConnected_geometricSpace P hconn
  refine ⟨x₀, subcomplex_space_subset_derivedNeighborhood hPK hx₀, fun {y} hy => ?_⟩
  exact ((hjoin (subcomplexBarycentricProjection_mem_subcomplex hPK hy)).mono
      (subcomplex_space_subset_derivedNeighborhood hPK)).trans
    (joinedIn_derivedNeighborhood_subcomplexBarycentricProjection hy).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPathConnected_derivedNeighborhood_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPathConnected_derivedNeighborhood_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPathConnected_derivedNeighborhood_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPathConnected_derivedNeighborhood_space

omit [FiniteDimensional ℝ E] in
open _root_.Classical in
theorem isConnected_derivedNeighborhood_space (hPK : P.faces ⊆ K.faces)
    (hconn : IsConnected P.space) : IsConnected (derivedNeighborhood K P).space :=
  (isPathConnected_derivedNeighborhood_space hPK hconn).isConnected

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_derivedNeighborhood_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConnected_derivedNeighborhood_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_derivedNeighborhood_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_derivedNeighborhood_space

omit [FiniteDimensional ℝ E] in
open _root_.Classical in
theorem isConnected_barycentricSubdivision_derivedNeighborhood_space (hPK : P.faces ⊆ K.faces)
    (hconn : IsConnected P.space) :
    IsConnected (barycentricSubdivision (derivedNeighborhood K P)).space := by
  rw [(barycentricSubdivision_isSubdivision (derivedNeighborhood K P)).space_eq]
  exact isConnected_derivedNeighborhood_space hPK hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_barycentricSubdivision_derivedNeighborhood_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isConnected_barycentricSubdivision_derivedNeighborhood_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isConnected_barycentricSubdivision_derivedNeighborhood_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isConnected_barycentricSubdivision_derivedNeighborhood_space

open _root_.Classical in
theorem exists_isGeneratedByPolygon_derivedNeighborhood (hPK : P.faces ⊆ K.faces)
    (hP : IsCombinatorialManifold 1 P) (hconn : IsConnected P.space) :
    ∃ (v₀ : (barycentricSubdivision (secondDerived P)).vertices)
      (γ₀ : (SimplicialComplex.edgeGraph
        (barycentricSubdivision (secondDerived P))).Walk v₀ v₀),
      IsGeneratedByPolygon (γ₀.map (edgeGraphHom (barycentricSubdivision_faces_subset
        (secondDerived_faces_subset_derivedNeighborhood hPK)))) := by
  have hQspace : (barycentricSubdivision (secondDerived P)).space = P.space :=
    (barycentricSubdivision_isSubdivision (secondDerived P)).space_eq.trans
      (secondDerived_isSubdivision P).space_eq
  have hQconn : IsConnected (barycentricSubdivision (secondDerived P)).space := by
    rw [hQspace]; exact hconn
  obtain ⟨v₀, γ₀, -, -, hgen₀⟩ :=
    exists_cycle_generating_loops hP.secondDerived.barycentricSubdivision hQconn
  refine ⟨v₀, γ₀, ?_⟩
  let c₁ : (barycentricSubdivision (secondDerived P)).space ≃ₜ P.space :=
    Homeomorph.setCongr hQspace
  let e := derivedNeighborhoodSubcomplexHomeomorph (K := K) hPK
  let c₂ : (derivedNeighborhood K P).space ≃ₜ
      (barycentricSubdivision (derivedNeighborhood K P)).space :=
    Homeomorph.setCongr (barycentricSubdivision_isSubdivision (derivedNeighborhood K
        P)).space_eq.symm
  have hgen₁ := exists_homotopic_loopZPow_of_homeomorph c₁ hgen₀
  have hgen₂ := exists_homotopic_loopZPow_of_homeomorph e.symm hgen₁
  have hgen₃ := exists_homotopic_loopZPow_of_strongDeformationRetract
    (derivedNeighborhoodStrongDeformationRetract hPK)
    (e.symm (c₁ (vertexPoint (barycentricSubdivision (secondDerived P)) v₀))).2 _ hgen₂
  have hgen₄ := exists_homotopic_loopZPow_of_homeomorph c₂ hgen₃
  have hmapeq : ((((walkPath γ₀).map c₁.continuous).map e.symm.continuous).map
      continuous_subtype_val).map c₂.continuous =
      (walkPath γ₀).map (spaceInclusion (barycentricSubdivision_faces_subset
        (secondDerived_faces_subset_derivedNeighborhood hPK))).continuous :=
    Path.ext (funext fun t => Subtype.ext rfl)
  refine isGeneratedByPolygon_of_forall_exists_homotopic_loopZPow
    (edgeGraph_connected_of_isConnected_space _
      (isConnected_barycentricSubdivision_derivedNeighborhood_space hPK hconn)).preconnected
    _ fun ℓ => ?_
  obtain ⟨k, hk⟩ := hgen₄ ℓ
  refine ⟨k, hk.trans ?_⟩
  rw [walkPath_map, hmapeq]
  exact Path.Homotopic.refl _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isGeneratedByPolygon_derivedNeighborhood

open _root_.Classical in
theorem isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon
    (hPK : P.faces ⊆ K.faces) (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hP : IsCombinatorialManifold 1 P) (hconn : IsConnected P.space)
    (hnull : ∀ (y : P.space) (ℓ : Path y y),
      (ℓ.map (spaceInclusion hPK).continuous).Homotopic
        (Path.refl (spaceInclusion hPK y))) :
    IsOrientable (n + 1) (derivedNeighborhood K P) := by
  obtain ⟨v₀, γ₀, hgen⟩ := exists_isGeneratedByPolygon_derivedNeighborhood hPK hP hconn
  have hQspace : (barycentricSubdivision (secondDerived P)).space = P.space :=
    (barycentricSubdivision_isSubdivision (secondDerived P)).space_eq.trans
      (secondDerived_isSubdivision P).space_eq
  let c₁ : (barycentricSubdivision (secondDerived P)).space ≃ₜ P.space :=
    Homeomorph.setCongr hQspace
  let c₃ : K.space ≃ₜ (barycentricSubdivision (secondDerived K)).space :=
    Homeomorph.setCongr (((barycentricSubdivision_isSubdivision (secondDerived K)).space_eq.trans
      (secondDerived_isSubdivision K).space_eq)).symm
  refine isOrientable_of_ambient_nullHomotopic_generated_polygon
    (derivedNeighborhood_faces_subset K P) hK.secondDerived (hK.derivedNeighborhood P)
    (fun s hs => Classical.choice (isOrientable_faceStarComplex hK.secondDerived hs))
    (edgeGraph_connected_of_isConnected_space _
      (isConnected_barycentricSubdivision_derivedNeighborhood_space hPK hconn)).preconnected
    _ hgen ?_
  have hnull' := (hnull (c₁ (vertexPoint (barycentricSubdivision (secondDerived P)) v₀))
    ((walkPath γ₀).map c₁.continuous)).map
      (c₃ : C(K.space, (barycentricSubdivision (secondDerived K)).space))
  rw [walkPath_map, walkPath_map]
  exact hnull'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon

open _root_.Classical in
theorem exists_cylindricalDiagram_isOrientable_derivedNeighborhood_of_nullHomotopic_polygon
    (hPK : P.faces ⊆ K.faces) (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hP : IsCombinatorialManifold 1 P) (hconn : IsConnected P.space)
    (hnull : ∀ (y : P.space) (ℓ : Path y y),
      (ℓ.map (spaceInclusion hPK).continuous).Homotopic
        (Path.refl (spaceInclusion hPK y))) :
    IsOrientable 3 (derivedNeighborhood K P) ∧
      ∃ φ : (Fin 3 → ℝ) × ℝ → E,
        IsCylindricalDiagram φ (stdSimplex ℝ (Fin 3)) (derivedNeighborhood K P).space :=
  ⟨isOrientable_derivedNeighborhood_of_ambient_nullHomotopic_polygon hPK hK hP hconn hnull,
    exists_cylindricalDiagram_derivedNeighborhood_circle K P hK hPK hP hconn⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_isOrientable_derivedNeighborhood_of_nullHomotopic_polygon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_isOrientable_derivedNeighborhood_of_nullHomotopic_polygon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_isOrientable_derivedNeighborhood_of_nullHomotopic_polygon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_cylindricalDiagram_isOrientable_derivedNeighborhood_of_nullHomotopic_polygon

end DifferentialGeometry.Topology.PiecewiseLinear
