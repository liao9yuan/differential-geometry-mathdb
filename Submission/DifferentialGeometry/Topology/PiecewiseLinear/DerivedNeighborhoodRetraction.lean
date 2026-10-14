/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.FundamentalGroup.HomotopyEquiv
import Submission.DifferentialGeometry.Topology.Homotopy.DeformationRetract
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedWeights
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology
open _root_.unitInterval
open _root_.Submission.DifferentialGeometry.Topology.Homotopy

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem simplicialComplex_vertices_finite (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] : K.vertices.Finite :=
  Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplex_vertices_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplex_vertices_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplex_vertices_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplex_vertices_finite

open _root_.Classical in
noncomputable def simplicialComplexVertices (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] : Finset E :=
  (simplicialComplex_vertices_finite K).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices

@[simp]
theorem mem_simplicialComplexVertices (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {v : E} : v ∈ simplicialComplexVertices K ↔ v ∈ K.vertices := by
  classical
  exact (simplicialComplex_vertices_finite K).mem_toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_simplicialComplexVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_simplicialComplexVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_simplicialComplexVertices ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_simplicialComplexVertices

open _root_.Classical in
noncomputable def barycentricCoordinate (K : Geometry.SimplicialComplex ℝ E)
    (v x : E) : ℝ :=
  simplicialMap K (fun w => if w = v then (1 : ℝ) else 0) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate

open _root_.Classical in
theorem barycentricCoordinate_eq (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (s : Set E))
    (v : E) : barycentricCoordinate K v x = if v ∈ s then weights s x v else 0 := by
  classical
  rw [barycentricCoordinate, simplicialMap_eq_of_mem K _ hs hx]
  by_cases hv : v ∈ s
  · simp [hv]
  · simp [hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_eq

theorem barycentricCoordinate_nonneg (K : Geometry.SimplicialComplex ℝ E)
    {x : E} (hx : x ∈ K.space) (v : E) : 0 ≤ barycentricCoordinate K v x := by
  classical
  rw [barycentricCoordinate_eq K (carrierFace_mem hx) (mem_convexHull_carrierFace hx)]
  split_ifs with hv
  · exact weights_nonneg (mem_convexHull_carrierFace hx) hv
  · exact le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_nonneg ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.barycentricCoordinate_nonneg

theorem continuousOn_barycentricCoordinate [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (v : E) :
    ContinuousOn (barycentricCoordinate K v) K.space :=
  by
    classical
    exact (isPiecewiseAffineOn_simplicialMap K
      (fun w => if w = v then (1 : ℝ) else 0)).continuousOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_barycentricCoordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_barycentricCoordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_barycentricCoordinate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_barycentricCoordinate

open _root_.Classical in
noncomputable def subcomplexBarycentricMass
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (x : E) : ℝ :=
  ∑ v ∈ (simplicialComplexVertices K).filter (· ∈ L.vertices),
    barycentricCoordinate K v x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass

open _root_.Classical in
noncomputable def subcomplexBarycentricMoment
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (x : E) : E :=
  ∑ v ∈ (simplicialComplexVertices K).filter (· ∈ L.vertices),
    barycentricCoordinate K v x • v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment

open _root_.Classical in
noncomputable def subcomplexBarycentricProjection
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (x : E) : E :=
  (subcomplexBarycentricMass K L x)⁻¹ • subcomplexBarycentricMoment K L x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection

theorem continuousOn_subcomplexBarycentricMass [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    ContinuousOn (subcomplexBarycentricMass K L) K.space := by
  classical
  exact continuousOn_finsetSum ((simplicialComplexVertices K).filter (· ∈ L.vertices)) fun v _ =>
    continuousOn_barycentricCoordinate K v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMass ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMass

theorem continuousOn_subcomplexBarycentricMoment [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    ContinuousOn (subcomplexBarycentricMoment K L) K.space := by
  classical
  exact continuousOn_finsetSum ((simplicialComplexVertices K).filter (· ∈ L.vertices)) fun v _ =>
    (continuousOn_barycentricCoordinate K v).smul continuousOn_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMoment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMoment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMoment ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricMoment

open _root_.Classical in
theorem barycentricSubdivision_filter_mem
    {K L : Geometry.SimplicialComplex ℝ E} (hL : L.faces ⊆ K.faces)
    {e : Finset E} (he : e ∈ (barycentricSubdivision K).faces)
    (hne : (e.filter fun v => v ∈ (barycentricSubdivision L).vertices).Nonempty) :
    e.filter (fun v => v ∈ (barycentricSubdivision L).vertices) ∈
      (barycentricSubdivision L).faces := by
  obtain ⟨d, hd, hdne, rfl⟩ := he
  let dL := d.filter fun s => s ∈ L.faces
  have hdL : IsFlag L dL := by
    refine ⟨fun s hs => (Finset.mem_filter.mp hs).2, fun s hs t ht => ?_⟩
    exact hd.subset_or_subset (Finset.mem_of_mem_filter s hs) (Finset.mem_of_mem_filter t ht)
  have himage :
      (d.image fun s => s.centroid ℝ id).filter
          (fun v => v ∈ (barycentricSubdivision L).vertices) =
        dL.image fun s => s.centroid ℝ id := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvimg, hvL⟩ := Finset.mem_filter.mp hv
      obtain ⟨s, hs, hsv⟩ := Finset.mem_image.mp hvimg
      obtain ⟨t, ht, htv⟩ :=
        exists_eq_centroid_of_singleton_mem_barycentricSubdivision L hvL
      have hst : s = t := injOn_faces_of_mem_openSimplex K
        (centroid_mem_openSimplex_of_mem_faces K) (hd.mem_faces hs) (hL ht)
        (hsv.trans htv.symm)
      refine Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, ?_⟩, hsv⟩
      exact hst ▸ ht
    · intro hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hsd, hsL⟩ := Finset.mem_filter.mp hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hsd, ?_⟩
      exact singleton_centroid_mem_barycentricSubdivision L hsL
  rw [himage] at hne ⊢
  exact ⟨dL, hdL, Finset.image_nonempty.mp hne, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_filter_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_filter_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_filter_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_filter_mem

open _root_.Classical in
theorem faceNeighborhood_faces_subset_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E}
    {e : Finset E} (he : e ∈ (barycentricSubdivision K).faces) :
    (faceNeighborhood e ((barycentricSubdivision K).indep he)
      (e.filter fun v => v ∈ (barycentricSubdivision L).vertices)).faces ⊆
        (derivedNeighborhood K L).faces := by
  rintro u ⟨d, hd, hchain, hne, hmeet, rfl⟩
  refine ⟨d, ⟨fun s hs => (barycentricSubdivision K).down_closed he
    (hd s hs).2 (hd s hs).1, hchain⟩, hne, ?_, rfl⟩
  intro s hs
  obtain ⟨v, hv⟩ := hmeet s hs
  obtain ⟨hvs, hve⟩ := Finset.mem_inter.mp hv
  obtain ⟨hve, hvL⟩ := Finset.mem_filter.mp hve
  obtain ⟨a, ha, hav⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision L hvL
  exact ⟨a, ha, hav ▸ hvs⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_faces_subset_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_faces_subset_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_faces_subset_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_faces_subset_derivedNeighborhood

open _root_.Classical in
theorem faceNeighborhood_space_subset_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E}
    {e : Finset E} (he : e ∈ (barycentricSubdivision K).faces) :
    (faceNeighborhood e ((barycentricSubdivision K).indep he)
      (e.filter fun v => v ∈ (barycentricSubdivision L).vertices)).space ⊆
        (derivedNeighborhood K L).space := by
  intro x hx
  obtain ⟨u, hu, hxu⟩ :=
    (faceNeighborhood e ((barycentricSubdivision K).indep he)
      (e.filter fun v => v ∈ (barycentricSubdivision L).vertices)).mem_space_iff.mp hx
  exact (derivedNeighborhood K L).convexHull_subset_space
    (faceNeighborhood_faces_subset_derivedNeighborhood he hu) hxu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_space_subset_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_space_subset_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_space_subset_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.faceNeighborhood_space_subset_derivedNeighborhood

open _root_.Classical in
theorem exists_faceNeighborhood_of_mem_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} {x : E}
    (hx : x ∈ (derivedNeighborhood K L).space) :
    ∃ e, ∃ he : e ∈ (barycentricSubdivision K).faces,
      (e.filter fun v => v ∈ (barycentricSubdivision L).vertices).Nonempty ∧
        x ∈ (faceNeighborhood e ((barycentricSubdivision K).indep he)
          (e.filter fun v => v ∈ (barycentricSubdivision L).vertices)).space := by
  obtain ⟨u, ⟨d, hd, hne, hmeet, rfl⟩, hxu⟩ :=
    (derivedNeighborhood K L).mem_space_iff.mp hx
  obtain ⟨e, he, htop⟩ := hd.exists_top hne
  have heK := hd.mem_faces he
  have hfne : (e.filter fun v => v ∈ (barycentricSubdivision L).vertices).Nonempty := by
    obtain ⟨a, ha, hae⟩ := hmeet e he
    refine ⟨a.centroid ℝ id, Finset.mem_filter.mpr ⟨hae, ?_⟩⟩
    exact singleton_centroid_mem_barycentricSubdivision L ha
  refine ⟨e, heK, hfne, (faceNeighborhood e ((barycentricSubdivision K).indep heK)
    (e.filter fun v => v ∈ (barycentricSubdivision L).vertices)).convexHull_subset_space ?_ hxu⟩
  exact ⟨d, fun s hs => ⟨(barycentricSubdivision K).nonempty_of_mem_faces (hd.mem_faces hs),
    htop s hs⟩, hd.2, hne, fun s hs => by
      obtain ⟨a, ha, has⟩ := hmeet s hs
      exact ⟨a.centroid ℝ id, Finset.mem_inter.mpr ⟨has, Finset.mem_filter.mpr
        ⟨htop s hs has, singleton_centroid_mem_barycentricSubdivision L ha⟩⟩⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_faceNeighborhood_of_mem_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_faceNeighborhood_of_mem_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_faceNeighborhood_of_mem_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_faceNeighborhood_of_mem_derivedNeighborhood

open _root_.Classical in
theorem simplicialComplexVertices_filter_eq
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) :
    ((simplicialComplexVertices K).filter (· ∈ L.vertices)).filter (· ∈ e) =
      e.filter (· ∈ L.vertices) := by
  ext v
  simp only [Finset.mem_filter, mem_simplicialComplexVertices]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨K.down_closed he (Finset.singleton_subset_iff.mpr h.1)
      (Finset.singleton_nonempty v), h.2⟩, h.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices_filter_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices_filter_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices_filter_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.simplicialComplexVertices_filter_eq

open _root_.Classical in
theorem subcomplexBarycentricMass_eq_sum_filter
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (e : Set E)) :
    subcomplexBarycentricMass K L x =
      ∑ v ∈ e.filter (· ∈ L.vertices), weights e x v := by
  rw [subcomplexBarycentricMass, ← simplicialComplexVertices_filter_eq K L he]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rw [barycentricCoordinate_eq K he hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_eq_sum_filter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_eq_sum_filter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_eq_sum_filter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_eq_sum_filter

open _root_.Classical in
theorem subcomplexBarycentricMoment_eq_sum_filter
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (e : Set E)) :
    subcomplexBarycentricMoment K L x =
      ∑ v ∈ e.filter (· ∈ L.vertices), weights e x v • v := by
  rw [subcomplexBarycentricMoment, ← simplicialComplexVertices_filter_eq K L he]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  rw [barycentricCoordinate_eq K he hx]
  by_cases hvL : v ∈ L.vertices <;> by_cases hve : v ∈ e <;> simp [hvL, hve]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment_eq_sum_filter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment_eq_sum_filter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment_eq_sum_filter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMoment_eq_sum_filter

open _root_.Classical in
theorem subcomplexBarycentricProjection_eq_of_faces_subset
    {K K' L L' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (hK : K.faces ⊆ K'.faces)
    (hvertices : ∀ v ∈ K.vertices, (v ∈ L.vertices ↔ v ∈ L'.vertices))
    {x : E} (hx : x ∈ K.space) :
    subcomplexBarycentricProjection K L x = subcomplexBarycentricProjection K' L' x := by
  let e := carrierFace K x
  have heK : e ∈ K.faces := carrierFace_mem hx
  have hxe : x ∈ convexHull ℝ (e : Set E) := mem_convexHull_carrierFace hx
  have hfilter : e.filter (· ∈ L.vertices) = e.filter (· ∈ L'.vertices) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hve, hvL⟩
      refine ⟨hve, (hvertices v ?_).mp hvL⟩
      exact K.down_closed heK (Finset.singleton_subset_iff.mpr hve)
        (Finset.singleton_nonempty v)
    · rintro ⟨hve, hvL⟩
      refine ⟨hve, (hvertices v ?_).mpr hvL⟩
      exact K.down_closed heK (Finset.singleton_subset_iff.mpr hve)
        (Finset.singleton_nonempty v)
  simp only [subcomplexBarycentricProjection]
  rw [
    subcomplexBarycentricMass_eq_sum_filter K L heK hxe,
    subcomplexBarycentricMass_eq_sum_filter K' L' (hK heK) hxe,
    subcomplexBarycentricMoment_eq_sum_filter K L heK hxe,
    subcomplexBarycentricMoment_eq_sum_filter K' L' (hK heK) hxe, hfilter]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_of_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_of_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_of_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_of_faces_subset

open _root_.Classical in
theorem subcomplexBarycentricMass_pos_of_mem_faceNeighborhood
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces)
    (hf : (e.filter fun v => v ∈ L.vertices).Nonempty) {x : E}
    (hx : x ∈ (faceNeighborhood e (K.indep he)
      (e.filter fun v => v ∈ L.vertices)).space) :
    0 < subcomplexBarycentricMass K L x := by
  obtain ⟨hxe, v, hvf, hmax⟩ :=
    (mem_faceNeighborhood_space_iff (K.indep he) (Finset.filter_subset _ _) hf).mp hx
  rw [subcomplexBarycentricMass_eq_sum_filter K L he hxe]
  have hnonneg : ∀ w ∈ e, 0 ≤ weights e x w := fun w hw => weights_nonneg hxe hw
  have hsumpos : 0 < ∑ w ∈ e, weights e x w := by rw [sum_weights hxe]; exact zero_lt_one
  obtain ⟨w, hw, hwpos⟩ := (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsumpos
  have hvpos : 0 < weights e x v := hwpos.trans_le (hmax w hw)
  exact Finset.sum_pos' (fun z hz => weights_nonneg hxe (Finset.mem_filter.mp hz).1)
    ⟨v, hvf, hvpos⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_of_mem_faceNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_of_mem_faceNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_of_mem_faceNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_of_mem_faceNeighborhood

open _root_.Classical in
theorem subcomplexBarycentricProjection_mem_convexHull_filter
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (e : Set E))
    (hmass : 0 < subcomplexBarycentricMass K L x) :
    subcomplexBarycentricProjection K L x ∈
      convexHull ℝ ((e.filter fun v => v ∈ L.vertices : Finset E) : Set E) := by
  let f := e.filter fun v => v ∈ L.vertices
  let m := subcomplexBarycentricMass K L x
  have hm : m ≠ 0 := hmass.ne'
  have hsum : ∑ v ∈ f, m⁻¹ * weights e x v = 1 := by
    rw [← Finset.mul_sum, ← subcomplexBarycentricMass_eq_sum_filter K L he hx]
    exact inv_mul_cancel₀ hm
  refine mem_convexHull_iff_exists_weights.mpr ⟨fun v => m⁻¹ * weights e x v,
    fun v hv => mul_nonneg (inv_nonneg.mpr hmass.le)
      (weights_nonneg hx (Finset.mem_filter.mp hv).1),
    hsum, ?_⟩
  rw [subcomplexBarycentricProjection, subcomplexBarycentricMoment_eq_sum_filter K L he hx]
  simp_rw [_root_.SemigroupAction.mul_smul]
  rw [Finset.smul_sum]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_convexHull_filter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_convexHull_filter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_convexHull_filter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_convexHull_filter

open _root_.Classical in
theorem weights_subcomplexBarycentricProjection
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (e : Set E))
    (hmass : 0 < subcomplexBarycentricMass K L x) {w : E} (hw : w ∈ e) :
    weights e (subcomplexBarycentricProjection K L x) w =
      if w ∈ e.filter (fun v => v ∈ L.vertices) then
        (subcomplexBarycentricMass K L x)⁻¹ * weights e x w else 0 := by
  let f := e.filter fun v => v ∈ L.vertices
  let m := subcomplexBarycentricMass K L x
  have hm : m ≠ 0 := hmass.ne'
  have hp := subcomplexBarycentricProjection_mem_convexHull_filter K L he hx hmass
  have hpE : subcomplexBarycentricProjection K L x ∈ convexHull ℝ (e : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hp
  apply weights_eq (K.indep he) hpE
      (w := fun v => if v ∈ f then m⁻¹ * weights e x v else 0)
  · rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
      ← Finset.mul_sum, ← subcomplexBarycentricMass_eq_sum_filter K L he hx]
    exact inv_mul_cancel₀ hm
  · simp_rw [ite_smul, zero_smul, _root_.SemigroupAction.mul_smul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
      ← Finset.smul_sum, ← subcomplexBarycentricMoment_eq_sum_filter K L he hx]
    rfl
  · exact hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.weights_subcomplexBarycentricProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.weights_subcomplexBarycentricProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.weights_subcomplexBarycentricProjection ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.weights_subcomplexBarycentricProjection

open _root_.Classical in
theorem subcomplexBarycentricProjection_eq_self
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : E} (hx : x ∈ L.space) :
    subcomplexBarycentricProjection K L x = x := by
  obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
  have hxK : x ∈ K.space := K.convexHull_subset_space (hL ht) hxt
  let e := carrierFace K x
  have heK : e ∈ K.faces := carrierFace_mem hxK
  have hxe : x ∈ convexHull ℝ (e : Set E) := mem_convexHull_carrierFace hxK
  have het : e ⊆ t := carrierFace_subset hxK (hL ht) hxt
  have heL : e ∈ L.faces := L.down_closed ht het (K.nonempty_of_mem_faces heK)
  have hfilter : e.filter (fun v => v ∈ L.vertices) = e := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact L.down_closed heL (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  rw [subcomplexBarycentricProjection, subcomplexBarycentricMass_eq_sum_filter K L heK hxe,
    subcomplexBarycentricMoment_eq_sum_filter K L heK hxe, hfilter, sum_weights hxe,
    inv_one, one_smul, sum_weights_smul hxe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self

open _root_.Classical in
theorem derivedNeighborhood_space_subset_barycentricSubdivision
    (K L : Geometry.SimplicialComplex ℝ E) :
    (derivedNeighborhood K L).space ⊆ (barycentricSubdivision K).space := by
  rw [(barycentricSubdivision_isSubdivision K).space_eq]
  exact derivedNeighborhood_space_subset K L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_barycentricSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_barycentricSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_barycentricSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhood_space_subset_barycentricSubdivision

open _root_.Classical in
theorem barycentricSubdivision_vertices_agree_of_restrict
    {K K' L L' : Geometry.SimplicialComplex ℝ E}
    (hK : K.faces ⊆ K'.faces) (hLK : L.faces ⊆ K.faces)
    (hL'K' : L'.faces ⊆ K'.faces)
    (hrestrict : ∀ s ∈ K.faces, (s ∈ L.faces ↔ s ∈ L'.faces))
    (v : E) (hv : v ∈ (barycentricSubdivision K).vertices) :
    v ∈ (barycentricSubdivision L).vertices ↔
      v ∈ (barycentricSubdivision L').vertices := by
  obtain ⟨s, hs, hsv⟩ :=
    exists_eq_centroid_of_singleton_mem_barycentricSubdivision K hv
  constructor
  · intro hvL
    obtain ⟨t, ht, htv⟩ :=
      exists_eq_centroid_of_singleton_mem_barycentricSubdivision L hvL
    have hst : s = t := injOn_faces_of_mem_openSimplex K
      (centroid_mem_openSimplex_of_mem_faces K) hs (hLK ht) (hsv.trans htv.symm)
    subst t
    exact hsv ▸ singleton_centroid_mem_barycentricSubdivision L' ((hrestrict s hs).mp ht)
  · intro hvL'
    obtain ⟨t, ht, htv⟩ :=
      exists_eq_centroid_of_singleton_mem_barycentricSubdivision L' hvL'
    have hst : s = t := injOn_faces_of_mem_openSimplex K'
      (centroid_mem_openSimplex_of_mem_faces K') (hK hs) (hL'K' ht)
      (hsv.trans htv.symm)
    subst t
    exact hsv ▸ singleton_centroid_mem_barycentricSubdivision L ((hrestrict s hs).mpr ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_vertices_agree_of_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_vertices_agree_of_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_vertices_agree_of_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.barycentricSubdivision_vertices_agree_of_restrict

open _root_.Classical in
theorem derivedNeighborhoodBarycentricProjection_eq_of_restrict
    {K K' L L' : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite K'.faces]
    (hK : K.faces ⊆ K'.faces) (hLK : L.faces ⊆ K.faces)
    (hL'K' : L'.faces ⊆ K'.faces)
    (hrestrict : ∀ s ∈ K.faces, (s ∈ L.faces ↔ s ∈ L'.faces))
    {x : E} (hx : x ∈ K.space) :
    subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x =
      subcomplexBarycentricProjection (barycentricSubdivision K')
        (barycentricSubdivision L') x := by
  apply subcomplexBarycentricProjection_eq_of_faces_subset
    (barycentricSubdivision_faces_subset hK)
    (barycentricSubdivision_vertices_agree_of_restrict hK hLK hL'K' hrestrict)
  rwa [(barycentricSubdivision_isSubdivision K).space_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodBarycentricProjection_eq_of_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodBarycentricProjection_eq_of_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodBarycentricProjection_eq_of_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodBarycentricProjection_eq_of_restrict

open _root_.Classical in
theorem subcomplexBarycentricMass_pos_on_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {x : E} (hx : x ∈ (derivedNeighborhood K L).space) :
    0 < subcomplexBarycentricMass (barycentricSubdivision K) (barycentricSubdivision L) x := by
  obtain ⟨e, he, hf, hxe⟩ := exists_faceNeighborhood_of_mem_derivedNeighborhood hx
  exact subcomplexBarycentricMass_pos_of_mem_faceNeighborhood
    (barycentricSubdivision K) (barycentricSubdivision L) he hf hxe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_on_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_on_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_on_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricMass_pos_on_derivedNeighborhood

open _root_.Classical in
theorem continuousOn_subcomplexBarycentricProjection_derivedNeighborhood
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    :
    ContinuousOn
      (subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L))
      (derivedNeighborhood K L).space := by
  have hsub := derivedNeighborhood_space_subset_barycentricSubdivision K L
  exact (((continuousOn_subcomplexBarycentricMass
    (barycentricSubdivision K) (barycentricSubdivision L)).mono hsub).inv₀
      (fun x hx => (subcomplexBarycentricMass_pos_on_derivedNeighborhood hx).ne')).smul
    ((continuousOn_subcomplexBarycentricMoment
      (barycentricSubdivision K) (barycentricSubdivision L)).mono hsub)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricProjection_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricProjection_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricProjection_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.continuousOn_subcomplexBarycentricProjection_derivedNeighborhood

open _root_.Classical in
theorem subcomplexBarycentricProjection_mem_subcomplex
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : E} (hx : x ∈ (derivedNeighborhood K L).space) :
    subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x ∈
      L.space := by
  obtain ⟨e, he, hf, hxe⟩ := exists_faceNeighborhood_of_mem_derivedNeighborhood hx
  have hxe' := (mem_faceNeighborhood_space_iff ((barycentricSubdivision K).indep he)
    (Finset.filter_subset _ _) hf).mp hxe
  have hp := subcomplexBarycentricProjection_mem_convexHull_filter
    (barycentricSubdivision K) (barycentricSubdivision L) he hxe'.1
      (subcomplexBarycentricMass_pos_on_derivedNeighborhood hx)
  rw [← (barycentricSubdivision_isSubdivision L).space_eq]
  exact (barycentricSubdivision L).convexHull_subset_space
    (barycentricSubdivision_filter_mem hL he hf) hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_subcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_subcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_subcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_subcomplex

open _root_.Classical in
noncomputable def subcomplexBarycentricHomotopy
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (t : I) (x : E) : E :=
  (1 - (t : ℝ)) • x + (t : ℝ) • subcomplexBarycentricProjection K L x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy

open _root_.Classical in
theorem subcomplexBarycentricHomotopy_mem_faceNeighborhood
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {e : Finset E} (he : e ∈ K.faces)
    (hf : (e.filter fun v => v ∈ L.vertices).Nonempty) {x : E}
    (hx : x ∈ (faceNeighborhood e (K.indep he)
      (e.filter fun v => v ∈ L.vertices)).space) (t : I) :
    subcomplexBarycentricHomotopy K L t x ∈
      (faceNeighborhood e (K.indep he)
        (e.filter fun v => v ∈ L.vertices)).space := by
  let f := e.filter fun v => v ∈ L.vertices
  let m := subcomplexBarycentricMass K L x
  let p := subcomplexBarycentricProjection K L x
  obtain ⟨hxe, v, hvf, hmax⟩ :=
    (mem_faceNeighborhood_space_iff (K.indep he) (Finset.filter_subset _ _) hf).mp hx
  have hm : 0 < m := subcomplexBarycentricMass_pos_of_mem_faceNeighborhood K L he hf hx
  have hpF : p ∈ convexHull ℝ ((f : Finset E) : Set E) :=
    subcomplexBarycentricProjection_mem_convexHull_filter K L he hxe hm
  have hpE : p ∈ convexHull ℝ (e : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hpF
  have hα : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have hβ : 0 ≤ (t : ℝ) := t.property.1
  have hsum : (1 - (t : ℝ)) + (t : ℝ) = 1 := by ring
  have hyE : subcomplexBarycentricHomotopy K L t x ∈ convexHull ℝ (e : Set E) := by
    exact (convex_convexHull ℝ _) hxe hpE hα hβ hsum
  refine (mem_faceNeighborhood_space_iff (K.indep he) (Finset.filter_subset _ _) hf).mpr
    ⟨hyE, v, hvf, ?_⟩
  intro w hw
  rw [subcomplexBarycentricHomotopy,
    weights_combo (K.indep he) hxe hpE hα hβ hsum w hw,
    weights_combo (K.indep he) hxe hpE hα hβ hsum v (Finset.mem_filter.mp hvf).1,
    weights_subcomplexBarycentricProjection K L he hxe hm hw,
    weights_subcomplexBarycentricProjection K L he hxe hm (Finset.mem_filter.mp hvf).1,
    if_pos hvf]
  have hinv : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  have hvnonneg : 0 ≤ weights e x v := weights_nonneg hxe (Finset.mem_filter.mp hvf).1
  by_cases hwf : w ∈ f
  · rw [if_pos hwf]
    exact add_le_add (mul_le_mul_of_nonneg_left (hmax w hw) hα)
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmax w hw) hinv) hβ)
  · rw [if_neg hwf, _root_.MulZeroClass.mul_zero, add_zero]
    exact (mul_le_mul_of_nonneg_left (hmax w hw) hα).trans
      (le_add_of_nonneg_right (mul_nonneg hβ (mul_nonneg hinv hvnonneg)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_faceNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_faceNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_faceNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_faceNeighborhood

open _root_.Classical in
theorem subcomplexBarycentricHomotopy_mem_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    {x : E} (hx : x ∈ (derivedNeighborhood K L).space) (t : I) :
    subcomplexBarycentricHomotopy (barycentricSubdivision K) (barycentricSubdivision L) t x ∈
      (derivedNeighborhood K L).space := by
  obtain ⟨e, he, hf, hxe⟩ := exists_faceNeighborhood_of_mem_derivedNeighborhood hx
  exact faceNeighborhood_space_subset_derivedNeighborhood he
    (subcomplexBarycentricHomotopy_mem_faceNeighborhood
      (barycentricSubdivision K) (barycentricSubdivision L) he hf hxe t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricHomotopy_mem_derivedNeighborhood

open _root_.Classical in
theorem subcomplex_space_subset_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) : L.space ⊆ (derivedNeighborhood K L).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
  have hxK : x ∈ K.space := K.convexHull_subset_space (hL hs) hxs
  exact mem_of_mem_nhdsWithin hxK (derivedNeighborhood_mem_nhdsWithin hL hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplex_space_subset_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplex_space_subset_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplex_space_subset_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplex_space_subset_derivedNeighborhood

open _root_.Classical in
theorem subcomplexBarycentricProjection_mem_derivedNeighborhood
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : E} (hx : x ∈ (derivedNeighborhood K L).space) :
    subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x ∈
      (derivedNeighborhood K L).space :=
  subcomplex_space_subset_derivedNeighborhood hL
    (subcomplexBarycentricProjection_mem_subcomplex hL hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_derivedNeighborhood then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_derivedNeighborhood"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_derivedNeighborhood ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_mem_derivedNeighborhood

open _root_.Classical in
theorem subcomplexBarycentricProjection_eq_self_on_subcomplex
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) {x : E} (hx : x ∈ L.space) :
    subcomplexBarycentricProjection (barycentricSubdivision K)
      (barycentricSubdivision L) x = x := by
  apply subcomplexBarycentricProjection_eq_self
    (barycentricSubdivision_faces_subset hL)
  rwa [(barycentricSubdivision_isSubdivision L).space_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self_on_subcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self_on_subcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self_on_subcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexBarycentricProjection_eq_self_on_subcomplex

open _root_.Classical in
abbrev derivedNeighborhoodSpace (K L : Geometry.SimplicialComplex ℝ E) :=
  (derivedNeighborhood K L).space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSpace

open _root_.Classical in
def derivedNeighborhoodSubcomplex (K L : Geometry.SimplicialComplex ℝ E) :
    Set (derivedNeighborhoodSpace K L) :=
  {x | (x : E) ∈ L.space}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodSubcomplex

open _root_.Classical in
noncomputable def derivedNeighborhoodRetraction
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) :
    C(derivedNeighborhoodSpace K L, derivedNeighborhoodSubcomplex K L) where
  toFun x :=
    ⟨⟨subcomplexBarycentricProjection (barycentricSubdivision K) (barycentricSubdivision L) x,
      subcomplexBarycentricProjection_mem_derivedNeighborhood hL x.2⟩,
      subcomplexBarycentricProjection_mem_subcomplex hL x.2⟩
  continuous_toFun := by
    have hp : Continuous (fun x : derivedNeighborhoodSpace K L =>
        subcomplexBarycentricProjection (barycentricSubdivision K)
          (barycentricSubdivision L) (x : E)) :=
      continuousOn_iff_continuous_domRestrict.mp
        continuousOn_subcomplexBarycentricProjection_derivedNeighborhood
    exact (hp.subtype_mk _).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetraction ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodRetraction

open _root_.Classical in
noncomputable def derivedNeighborhoodHomotopyMap
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    C(I × derivedNeighborhoodSpace K L, derivedNeighborhoodSpace K L) where
  toFun z := ⟨subcomplexBarycentricHomotopy (barycentricSubdivision K)
    (barycentricSubdivision L) z.1 z.2,
      subcomplexBarycentricHomotopy_mem_derivedNeighborhood z.2.2 z.1⟩
  continuous_toFun := by
    have ht : Continuous (fun z : I × derivedNeighborhoodSpace K L => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun z : I × derivedNeighborhoodSpace K L => (z.2 : E)) :=
      continuous_subtype_val.comp continuous_snd
    have hp : Continuous (fun x : derivedNeighborhoodSpace K L =>
        subcomplexBarycentricProjection (barycentricSubdivision K)
          (barycentricSubdivision L) (x : E)) :=
      continuousOn_iff_continuous_domRestrict.mp
        continuousOn_subcomplexBarycentricProjection_derivedNeighborhood
    exact ((continuous_const.sub ht).smul hx |>.add (ht.smul (hp.comp continuous_snd))).subtype_mk _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyMap ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodHomotopyMap

open _root_.Classical in
noncomputable def derivedNeighborhoodStrongDeformationRetract
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) :
    StrongDeformationRetract (derivedNeighborhoodSubcomplex K L) where
  retraction := derivedNeighborhoodRetraction hL
  homotopy := {
    toHomotopy := {
      toContinuousMap := derivedNeighborhoodHomotopyMap K L
      map_zero_left := by
        intro x
        apply Subtype.ext
        simp [derivedNeighborhoodHomotopyMap, subcomplexBarycentricHomotopy]
      map_one_left := by
        intro x
        apply Subtype.ext
        simp [derivedNeighborhoodHomotopyMap, subcomplexBarycentricHomotopy,
          derivedNeighborhoodRetraction]
    }
    prop' := by
      intro t x hx
      apply Subtype.ext
      change (1 - (t : ℝ)) • (x : E) + (t : ℝ) •
        subcomplexBarycentricProjection (barycentricSubdivision K)
          (barycentricSubdivision L) x = x
      rw [subcomplexBarycentricProjection_eq_self_on_subcomplex hL hx]
      rw [← add_smul, sub_add_cancel, one_smul]
  }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract

open _root_.Classical in
theorem derivedNeighborhoodStrongDeformationRetract_retraction_apply
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (x : derivedNeighborhoodSpace K L) :
    ((((derivedNeighborhoodStrongDeformationRetract hL).retraction x :
      derivedNeighborhoodSubcomplex K L) : derivedNeighborhoodSpace K L) : E) =
        subcomplexBarycentricProjection (barycentricSubdivision K)
          (barycentricSubdivision L) x :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract_retraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract_retraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract_retraction_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodStrongDeformationRetract_retraction_apply

open _root_.Classical in
noncomputable def derivedNeighborhoodCompatibleStrongDeformationRetractSystem
    [FiniteDimensional ℝ E]
    (K L : ℕ → Geometry.SimplicialComplex ℝ E) [∀ i, Finite (K i).faces]
    (hLK : ∀ i, (L i).faces ⊆ (K i).faces)
    (hK : Monotone fun i => (K i).faces) (hL : Monotone fun i => (L i).faces)
    (hrestrict : ∀ {i j}, i ≤ j → ∀ s ∈ (K i).faces,
      s ∈ (L j).faces → s ∈ (L i).faces)
    (hnhds : ∀ i {x : E}, x ∈ (derivedNeighborhood (K i) (L i)).space →
      (derivedNeighborhood (K (i + 1)) (L (i + 1))).space ∈
        𝓝[⋃ j, (derivedNeighborhood (K j) (L j)).space] x) :
    CompatibleStrongDeformationRetractSystem
      (fun i => (L i).space) (fun i => (derivedNeighborhood (K i) (L i)).space) where
  core_subset := fun i => subcomplex_space_subset_derivedNeighborhood (hLK i)
  stage := fun i => derivedNeighborhoodStrongDeformationRetract (hLK i)
  retraction_compatible := by
    intro i j hij x hxi hxj
    change subcomplexBarycentricProjection (barycentricSubdivision (K j))
      (barycentricSubdivision (L j)) x =
        subcomplexBarycentricProjection (barycentricSubdivision (K i))
          (barycentricSubdivision (L i)) x
    apply (derivedNeighborhoodBarycentricProjection_eq_of_restrict
      (hK hij) (hLK i) (hLK j) ?_ (derivedNeighborhood_space_subset (K i) (L i) hxi)).symm
    intro s hs
    exact ⟨fun hsL => hL hij hsL, hrestrict hij s hs⟩
  homotopy_compatible := by
    intro i j hij t x hxi hxj
    change subcomplexBarycentricHomotopy (barycentricSubdivision (K j))
      (barycentricSubdivision (L j)) t x =
        subcomplexBarycentricHomotopy (barycentricSubdivision (K i))
          (barycentricSubdivision (L i)) t x
    unfold subcomplexBarycentricHomotopy
    rw [derivedNeighborhoodBarycentricProjection_eq_of_restrict
      (hK hij) (hLK i) (hLK j) (fun s hs =>
        ⟨fun hsL => hL hij hsL, hrestrict hij s hs⟩)
      (derivedNeighborhood_space_subset (K i) (L i) hxi)]
  ambient_mem_nhdsWithin := by
    intro i x hx
    exact hnhds i hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCompatibleStrongDeformationRetractSystem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCompatibleStrongDeformationRetractSystem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCompatibleStrongDeformationRetractSystem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCompatibleStrongDeformationRetractSystem

open _root_.Classical in
noncomputable def derivedNeighborhoodFundamentalGroupEquiv
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (x : derivedNeighborhoodSubcomplex K L) :
    FundamentalGroup (derivedNeighborhoodSpace K L) x.1 ≃*
      FundamentalGroup (derivedNeighborhoodSubcomplex K L) x := by
  let r := derivedNeighborhoodStrongDeformationRetract hL
  apply DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    r.toHomotopyEquiv x.1 x
  apply Subtype.ext
  exact r.retraction_eq x.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupEquiv

open _root_.Classical in
noncomputable def derivedNeighborhoodFundamentalGroupInclusionEquiv
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (x : derivedNeighborhoodSubcomplex K L) :
    FundamentalGroup (derivedNeighborhoodSubcomplex K L) x ≃*
      FundamentalGroup (derivedNeighborhoodSpace K L) x.1 :=
  DifferentialGeometry.Topology.fundamentalGroupMulEquivOfHomotopyEquiv
    (derivedNeighborhoodStrongDeformationRetract hL).toHomotopyEquiv.symm x x.1 rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv

open _root_.Classical in
theorem derivedNeighborhoodFundamentalGroupInclusionEquiv_apply
    [FiniteDimensional ℝ E] {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hL : L.faces ⊆ K.faces) (x : derivedNeighborhoodSubcomplex K L)
    (g : FundamentalGroup (derivedNeighborhoodSubcomplex K L) x) :
    derivedNeighborhoodFundamentalGroupInclusionEquiv hL x g =
      FundamentalGroup.map
        ((ContinuousMap.id (derivedNeighborhoodSpace K L)).restrict
          (derivedNeighborhoodSubcomplex K L)) x g :=
  by
    change FundamentalGroup.mapOfEq
      ((ContinuousMap.id (derivedNeighborhoodSpace K L)).restrict
        (derivedNeighborhoodSubcomplex K L)) rfl g = _
    rw [FundamentalGroup.mapOfEq_apply]
    exact eq_of_heq (Path.Homotopic.Quotient.cast_heq rfl rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv_apply ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodFundamentalGroupInclusionEquiv_apply

end DifferentialGeometry.Topology.PiecewiseLinear
