/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Star

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def regularNeighborhoodFaces (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    Set (Finset E) :=
  {t ∈ K.faces | ∃ u ∈ K.faces, t ⊆ u ∧ (convexHull ℝ (u : Set E) ∩ A).Nonempty}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodFaces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodFaces

def regularNeighborhoodIn (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := regularNeighborhoodFaces K A
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1
  isRelLowerSet_faces := by
    rintro t ⟨ht, u, hu, htu, hA⟩
    exact ⟨K.nonempty_of_mem_faces ht, fun t' ht't ht' =>
      ⟨K.down_closed ht ht't ht', u, hu, ht't.trans htu, hA⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn

theorem mem_regularNeighborhoodIn_faces_iff (K : Geometry.SimplicialComplex ℝ E) (A : Set E)
    {t : Finset E} : t ∈ (regularNeighborhoodIn K A).faces ↔
      t ∈ K.faces ∧ ∃ u ∈ K.faces, t ⊆ u ∧ (convexHull ℝ (u : Set E) ∩ A).Nonempty :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_regularNeighborhoodIn_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_regularNeighborhoodIn_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_regularNeighborhoodIn_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_regularNeighborhoodIn_faces_iff

theorem regularNeighborhoodIn_le (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    regularNeighborhoodIn K A ≤ K :=
  fun _ ht => ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_le

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhoodIn (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (A : Set E) :
    Finite (regularNeighborhoodIn K A).faces :=
  ((Set.toFinite K.faces).subset fun _ ht => ht.1).to_subtype

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhoodIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhoodIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhoodIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhoodIn

theorem space_regularNeighborhoodIn_subset (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    (regularNeighborhoodIn K A).space ⊆ K.space := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := (regularNeighborhoodIn K A).mem_space_iff.mp hx
  exact K.convexHull_subset_space ht.1 hxt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhoodIn_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhoodIn_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhoodIn_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhoodIn_subset

theorem closedStar_subset_regularNeighborhoodIn (K : Geometry.SimplicialComplex ℝ E) (A : Set E)
    {x : E} (hx : x ∈ A) : closedStar K x ⊆ (regularNeighborhoodIn K A).space := by
  intro y hy
  unfold closedStar at hy
  rw [_root_.Set.mem_iUnion₂] at hy
  obtain ⟨s, ⟨hs, hxs⟩, hys⟩ := hy
  exact (regularNeighborhoodIn K A).convexHull_subset_space
    ⟨hs, s, hs, Finset.Subset.refl s, ⟨x, hxs, hx⟩⟩ hys

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_regularNeighborhoodIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_regularNeighborhoodIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_regularNeighborhoodIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_regularNeighborhoodIn

theorem regularNeighborhoodIn_mem_nhdsWithin (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (A : Set E) {x : E} (hx : x ∈ A) :
    (regularNeighborhoodIn K A).space ∈ 𝓝[K.space] x :=
  Filter.mem_of_superset (closedStar_mem_nhdsWithin K x)
    (closedStar_subset_regularNeighborhoodIn K A hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhoodIn_mem_nhdsWithin

variable [DecidableEq E]

noncomputable def secondDerived (K : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E :=
  barycentricSubdivision (barycentricSubdivision K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.secondDerived"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.secondDerived

theorem secondDerived_isSubdivision (K : Geometry.SimplicialComplex ℝ E) :
    IsSubdivision (secondDerived K) K :=
  (barycentricSubdivision_isSubdivision _).trans (barycentricSubdivision_isSubdivision K)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_isSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_isSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_isSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_isSubdivision

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesSecondDerived (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (secondDerived K).faces :=
  inferInstanceAs (Finite (barycentricSubdivision (barycentricSubdivision K)).faces)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesSecondDerived then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesSecondDerived"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesSecondDerived ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesSecondDerived

noncomputable def regularNeighborhood (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    Geometry.SimplicialComplex ℝ E :=
  regularNeighborhoodIn (secondDerived K) A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood

theorem regularNeighborhood_le (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    regularNeighborhood K A ≤ secondDerived K :=
  regularNeighborhoodIn_le _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_le

instance _root_.Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhood (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (A : Set E) :
    Finite (regularNeighborhood K A).faces :=
  inferInstanceAs (Finite (regularNeighborhoodIn (secondDerived K) A).faces)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.instFiniteElemFinsetFacesRegularNeighborhood

theorem space_regularNeighborhood_subset (K : Geometry.SimplicialComplex ℝ E) (A : Set E) :
    (regularNeighborhood K A).space ⊆ K.space :=
  (space_regularNeighborhoodIn_subset _ _).trans (secondDerived_isSubdivision K).space_eq.subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhood_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhood_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhood_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.space_regularNeighborhood_subset

theorem regularNeighborhood_mem_nhdsWithin (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (A : Set E) {x : E} (hx : x ∈ A) : (regularNeighborhood K A).space ∈ 𝓝[K.space] x := by
  rw [← (secondDerived_isSubdivision K).space_eq]
  exact regularNeighborhoodIn_mem_nhdsWithin (secondDerived K) A hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.regularNeighborhood_mem_nhdsWithin

end DifferentialGeometry.Topology.PiecewiseLinear
