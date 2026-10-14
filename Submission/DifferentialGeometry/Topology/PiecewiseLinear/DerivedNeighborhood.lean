/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FaceLink
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RegularNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFlag.of_le {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {d : Finset (Finset E)} (hd : IsFlag L d) : IsFlag K d :=
  ⟨fun s hs => hL (hd.1 s hs), hd.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsFlag.of_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsFlag.of_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsFlag.of_le ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsFlag.of_le

section Derived

variable [DecidableEq E] {K L : Geometry.SimplicialComplex ℝ E}

theorem barycentricSubdivision_faces_subset (hL : L.faces ⊆ K.faces) :
    (barycentricSubdivision L).faces ⊆ (barycentricSubdivision K).faces := by
  rintro u ⟨d, hd, hne, rfl⟩
  exact ⟨d, hd.of_le hL, hne, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_faces_subset

theorem secondDerived_faces_subset (hL : L.faces ⊆ K.faces) :
    (secondDerived L).faces ⊆ (secondDerived K).faces :=
  barycentricSubdivision_faces_subset (barycentricSubdivision_faces_subset hL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.secondDerived_faces_subset

theorem exists_mem_image_centroid_of_mem_barycentricSubdivision {e : Finset E}
    (he : e ∈ (barycentricSubdivision L).faces) : ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e := by
  obtain ⟨d, hd, hne, rfl⟩ := he
  obtain ⟨σ, hσ⟩ := hne
  exact ⟨σ, hd.mem_faces hσ, Finset.mem_image_of_mem _ hσ⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_image_centroid_of_mem_barycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_image_centroid_of_mem_barycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_image_centroid_of_mem_barycentricSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_mem_image_centroid_of_mem_barycentricSubdivision

end Derived

section Neighborhood

variable [DecidableEq E] (K L : Geometry.SimplicialComplex ℝ E)

def derivedNeighborhoodFaces : Set (Finset E) :=
  {u | ∃ D : Finset (Finset E), IsFlag (barycentricSubdivision K) D ∧ D.Nonempty ∧
    (∀ e ∈ D, ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e) ∧ u = D.image fun e => e.centroid ℝ id}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces

theorem derivedNeighborhoodFaces_subset :
    derivedNeighborhoodFaces K L ⊆ (secondDerived K).faces := by
  rintro u ⟨D, hD, hne, -, rfl⟩
  exact ⟨D, hD, hne, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_subset

theorem derivedNeighborhoodFaces_isRelLowerSet :
    IsRelLowerSet (derivedNeighborhoodFaces K L) Finset.Nonempty := by
  rintro u ⟨D, hD, hne, hL, rfl⟩
  refine ⟨hne.image _, fun g hgu hg => ?_⟩
  refine ⟨D.filter fun e => e.centroid ℝ id ∈ g, hD.mono (Finset.filter_subset _ _), ?_,
    fun e he => hL e (Finset.mem_of_mem_filter e he), (image_filter_mem_eq hgu).symm⟩
  obtain ⟨p, hp⟩ := hg
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp (hgu hp)
  exact ⟨e, Finset.mem_filter.mpr ⟨he, hp⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_isRelLowerSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_isRelLowerSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_isRelLowerSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFaces_isRelLowerSet

def derivedNeighborhood : Geometry.SimplicialComplex ℝ E where
  faces := derivedNeighborhoodFaces K L
  isRelLowerSet_faces := derivedNeighborhoodFaces_isRelLowerSet K L
  indep hs := (secondDerived K).indep (derivedNeighborhoodFaces_subset K L hs)
  inter_subset_convexHull hs ht := (secondDerived K).inter_subset_convexHull
    (derivedNeighborhoodFaces_subset K L hs) (derivedNeighborhoodFaces_subset K L ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood

theorem mem_derivedNeighborhood_faces_iff {u : Finset E} :
    u ∈ (derivedNeighborhood K L).faces ↔ ∃ D : Finset (Finset E),
      IsFlag (barycentricSubdivision K) D ∧ D.Nonempty ∧
        (∀ e ∈ D, ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e) ∧
        u = D.image fun e => e.centroid ℝ id := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_derivedNeighborhood_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_derivedNeighborhood_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_derivedNeighborhood_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_derivedNeighborhood_faces_iff

theorem derivedNeighborhood_faces_subset :
    (derivedNeighborhood K L).faces ⊆ (secondDerived K).faces :=
  derivedNeighborhoodFaces_subset K L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_subset

theorem derivedNeighborhood_faces_finite [Finite K.faces] :
    (derivedNeighborhood K L).faces.Finite :=
  (Set.toFinite (secondDerived K).faces).subset (derivedNeighborhood_faces_subset K L)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_finite

theorem derivedNeighborhood_faces_mono
    {K K' L L' : Geometry.SimplicialComplex ℝ E}
    (hK : K.faces ⊆ K'.faces) (hL : L.faces ⊆ L'.faces) :
    (derivedNeighborhood K L).faces ⊆ (derivedNeighborhood K' L').faces := by
  rintro u ⟨D, hD, hne, hmeet, rfl⟩
  refine ⟨D, hD.of_le (barycentricSubdivision_faces_subset hK), hne, ?_, rfl⟩
  intro e he
  obtain ⟨s, hs, hse⟩ := hmeet e he
  exact ⟨s, hL hs, hse⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_faces_mono

theorem derivedNeighborhood_space_subset_secondDerived :
    (derivedNeighborhood K L).space ⊆ (secondDerived K).space := by
  intro x hx
  obtain ⟨u, hu, hxu⟩ := (derivedNeighborhood K L).mem_space_iff.mp hx
  exact (secondDerived K).convexHull_subset_space (derivedNeighborhood_faces_subset K L hu) hxu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_secondDerived then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_secondDerived"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_secondDerived ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_secondDerived

theorem derivedNeighborhood_space_subset : (derivedNeighborhood K L).space ⊆ K.space :=
  (derivedNeighborhood_space_subset_secondDerived K L).trans
    (secondDerived_isSubdivision K).space_eq.subset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset

theorem singleton_centroid_mem_derivedNeighborhood_iff {e : Finset E}
    (he : e ∈ (barycentricSubdivision K).faces) :
    {e.centroid ℝ id} ∈ (derivedNeighborhood K L).faces ↔ ∃ σ ∈ L.faces, σ.centroid ℝ id ∈ e := by
  constructor
  · rintro ⟨D, hD, hne, hL, hD'⟩
    obtain ⟨e', he'⟩ := hne
    have hmem : e'.centroid ℝ id ∈ ({e.centroid ℝ id} : Finset E) := by
      rw [hD']
      exact Finset.mem_image_of_mem _ he'
    have heq : e' = e := injOn_faces_of_mem_openSimplex (barycentricSubdivision K)
      (centroid_mem_openSimplex_of_mem_faces _) (hD.mem_faces he') he
      (Finset.mem_singleton.mp hmem)
    exact heq ▸ hL e' he'
  · intro h
    exact ⟨{e}, ⟨fun s hs => (Finset.mem_singleton.mp hs).symm ▸ he,
      fun s hs t ht => Or.inl
        ((Finset.mem_singleton.mp hs).trans (Finset.mem_singleton.mp ht).symm ▸
          Finset.Subset.refl _)⟩, Finset.singleton_nonempty e,
      fun s hs => (Finset.mem_singleton.mp hs).symm ▸ h, by rw [Finset.image_singleton]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.singleton_centroid_mem_derivedNeighborhood_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.singleton_centroid_mem_derivedNeighborhood_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.singleton_centroid_mem_derivedNeighborhood_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.singleton_centroid_mem_derivedNeighborhood_iff

theorem subset_of_image_centroid_subset {D D' : Finset (Finset E)}
    (hD : IsFlag (barycentricSubdivision K) D) (hD' : IsFlag (barycentricSubdivision K) D')
    (h : (D'.image fun e => e.centroid ℝ id) ⊆ D.image fun e => e.centroid ℝ id) : D' ⊆ D := by
  intro e' he'
  obtain ⟨e, he, heq⟩ := Finset.mem_image.mp (h (Finset.mem_image_of_mem _ he'))
  have := injOn_faces_of_mem_openSimplex (barycentricSubdivision K)
    (centroid_mem_openSimplex_of_mem_faces _) (hD.mem_faces he) (hD'.mem_faces he') heq
  exact this ▸ he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subset_of_image_centroid_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subset_of_image_centroid_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subset_of_image_centroid_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subset_of_image_centroid_subset

end Neighborhood

section Nhds

variable [DecidableEq E] {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)

include hL

theorem closedStar_subset_derivedNeighborhood {x : E} (hx : x ∈ L.space) :
    closedStar (secondDerived K) x ⊆ (derivedNeighborhood K L).space := by
  intro y hy
  obtain ⟨u, ⟨hu, hxu⟩, hyu⟩ := mem_iUnion₂.mp hy
  have hxL : x ∈ (secondDerived L).space := (secondDerived_isSubdivision L).space_eq ▸ hx
  obtain ⟨uL, huL, hxuL⟩ := (secondDerived L).mem_space_iff.mp hxL
  have hxK : x ∈ (secondDerived K).space :=
    (secondDerived K).convexHull_subset_space hu hxu
  obtain ⟨u₀, hu₀, hxu₀⟩ := exists_face_mem_openSimplex (secondDerived K) hxK
  have hsub₀ : u₀ ⊆ u := face_subset_of_mem_openSimplex_of_mem_convexHull _ hu₀ hu hxu₀ hxu
  have hsubL : u₀ ⊆ uL := face_subset_of_mem_openSimplex_of_mem_convexHull _ hu₀
    (secondDerived_faces_subset hL huL) hxu₀ hxuL
  have huN : u ∈ (derivedNeighborhood K L).faces := by
    obtain ⟨D₀, hD₀, hne₀, rfl⟩ := hu₀
    obtain ⟨DL, hDL, -, rfl⟩ := huL
    obtain ⟨D, hD, hne, rfl⟩ := hu
    have hDL' : IsFlag (barycentricSubdivision K) DL :=
      hDL.of_le (barycentricSubdivision_faces_subset hL)
    have hD₀D : D₀ ⊆ D := subset_of_image_centroid_subset K hD hD₀ hsub₀
    have hD₀L : D₀ ⊆ DL := subset_of_image_centroid_subset K hDL' hD₀ hsubL
    refine ⟨D, hD, hne, fun e he => ?_, rfl⟩
    obtain ⟨e₀, he₀⟩ := hne₀
    have he₀L : e₀ ∈ (barycentricSubdivision L).faces := hDL.mem_faces (hD₀L he₀)
    rcases hD.subset_or_subset (hD₀D he₀) he with h | h
    · obtain ⟨σ, hσ, hσe₀⟩ := exists_mem_image_centroid_of_mem_barycentricSubdivision he₀L
      exact ⟨σ, hσ, h hσe₀⟩
    · exact exists_mem_image_centroid_of_mem_barycentricSubdivision
        ((barycentricSubdivision L).down_closed he₀L h
          ((barycentricSubdivision K).nonempty_of_mem_faces (hD.mem_faces he)))
  exact (derivedNeighborhood K L).convexHull_subset_space huN hyu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.closedStar_subset_derivedNeighborhood

theorem derivedNeighborhood_mem_nhdsWithin [Finite K.faces] {x : E} (hx : x ∈ L.space) :
    (derivedNeighborhood K L).space ∈ 𝓝[K.space] x := by
  rw [← (secondDerived_isSubdivision K).space_eq]
  exact Filter.mem_of_superset (closedStar_mem_nhdsWithin (secondDerived K) x)
    (closedStar_subset_derivedNeighborhood hL hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_mem_nhdsWithin

end Nhds

end DifferentialGeometry.Topology.PiecewiseLinear
