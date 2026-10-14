/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section Restrict

variable (K : Geometry.SimplicialComplex ℝ E) (Q : Set E)

def restrict : Geometry.SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ Q}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsQ⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht => ⟨K.down_closed hs hts ht,
      (convexHull_mono (Finset.coe_subset.mpr hts)).trans hsQ⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict

theorem mem_restrict_faces_iff {s : Finset E} :
    s ∈ (restrict K Q).faces ↔ s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ Q := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_restrict_faces_iff

theorem restrict_faces_subset : (restrict K Q).faces ⊆ K.faces := fun _ hs => hs.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_subset

theorem restrict_faces_finite [Finite K.faces] : (restrict K Q).faces.Finite :=
  (Set.toFinite K.faces).subset (restrict_faces_subset K Q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_faces_finite

theorem restrict_space_subset : (restrict K Q).space ⊆ Q := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (restrict K Q).mem_space_iff.mp hx
  exact hs.2 hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_subset

theorem restrict_space_of_eq_biUnion
    (h : Q = ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ Q}, convexHull ℝ (s : Set E)) :
    (restrict K Q).space = Q :=
  h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_eq_biUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_eq_biUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_eq_biUnion ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_of_eq_biUnion

theorem restrict_restrict (R : Set E) : restrict (restrict K Q) R = restrict K (Q ∩ R) := by
  ext s
  change ((s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ Q) ∧
    convexHull ℝ (s : Set E) ⊆ R) ↔ s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ Q ∩ R
  rw [_root_.Set.subset_inter_iff]
  tauto

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_restrict

variable {K Q}

theorem restrict_space_mono {R : Set E} (hQR : Q ⊆ R) :
    (restrict K Q).space ⊆ (restrict K R).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (restrict K Q).mem_space_iff.mp hx
  exact (restrict K R).convexHull_subset_space ⟨hs.1, hs.2.trans hQR⟩ hxs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_mono ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_space_mono

theorem restrict_convexHull_space {s : Finset E} (hs : s ∈ K.faces) :
    (restrict K (convexHull ℝ (s : Set E))).space = convexHull ℝ (s : Set E) :=
  Subset.antisymm (restrict_space_subset _ _)
    ((restrict K _).convexHull_subset_space ⟨hs, subset_rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_convexHull_space

theorem restrict_union_space {P : Set E} (hP : (restrict K P).space = P)
    (hQ : (restrict K Q).space = Q) : (restrict K (P ∪ Q)).space = P ∪ Q := by
  refine Subset.antisymm (restrict_space_subset _ _) (_root_.Set.union_subset ?_ ?_)
  · exact hP.symm.subset.trans (restrict_space_mono _root_.Set.subset_union_left)
  · exact hQ.symm.subset.trans (restrict_space_mono _root_.Set.subset_union_right)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_union_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_union_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_union_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_union_space

theorem restrict_isSubdivision (L : Geometry.SimplicialComplex ℝ E)
    (hL : ∀ t ∈ L.faces, convexHull ℝ (t : Set E) =
      ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)},
        convexHull ℝ (s : Set E)) :
    IsSubdivision (restrict K L.space) L := by
  refine ⟨Subset.antisymm (restrict_space_subset K L.space) fun x hx => ?_, ?_⟩
  · obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
    rw [hL t ht] at hxt
    obtain ⟨s, ⟨hs, hst⟩, hxs⟩ := mem_iUnion₂.mp hxt
    exact (restrict K L.space).convexHull_subset_space
      ⟨hs, hst.trans (L.convexHull_subset_space ht)⟩ hxs
  · rintro s ⟨hs, hsL⟩
    have hx : s.centroid ℝ id ∈ openSimplex s := centroid_mem_openSimplex (K.nonempty_of_mem_faces
        hs)
    have hxL : s.centroid ℝ id ∈ L.space := hsL (openSimplex_subset_convexHull s hx)
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
    rw [hL t ht] at hxt
    obtain ⟨s', ⟨hs', hs't⟩, hxs'⟩ := mem_iUnion₂.mp hxt
    refine ⟨t, ht, (convexHull_mono ?_).trans hs't⟩
    exact Finset.coe_subset.mpr (face_subset_of_mem_openSimplex_of_mem_convexHull K hs hs' hx hxs')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.restrict_isSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.restrict_isSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.restrict_isSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.restrict_isSubdivision

theorem exists_isSubdivision_restrict_space [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {Q : Set E} (hQ : IsPolyhedron Q)
    (hQK : Q ⊆ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (restrict K' Q).space = Q := by
  obtain ⟨K', hK', hfin, hQ'⟩ :=
    exists_isSubdivision_subcomplexes K (fun _ : Unit => Q) (fun _ => hQ) fun _ => hQK
  exact ⟨K', hK', hfin, restrict_space_of_eq_biUnion K' Q (hQ' ())⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_space

theorem exists_isSubdivision_restrict_isSubdivision [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hLK : L.space ⊆ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      IsSubdivision (restrict K' L.space) L := by
  obtain ⟨K', hK', hfin, hQ'⟩ := exists_isSubdivision_subcomplexes K
    (fun t : L.faces => convexHull ℝ ((t : Finset E) : Set E))
    (fun t => isPolyhedron_convexHull_of_affineIndependent _ (L.indep t.2))
    fun t => (L.convexHull_subset_space t.2).trans hLK
  exact ⟨K', hK', hfin, restrict_isSubdivision L fun t ht => hQ' ⟨t, ht⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_isSubdivision then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_isSubdivision"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_isSubdivision ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_restrict_isSubdivision

theorem IsSubdivision.restrict {R : Geometry.SimplicialComplex ℝ E}
    (hR : IsSubdivision R K) (L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) :
    IsSubdivision (restrict R L.space) L :=
  restrict_isSubdivision L fun _ ht => hR.convexHull_eq_biUnion (hLK ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.restrict ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsSubdivision.restrict

theorem exists_isSubdivision_subcomplexes_closedStars_subset_cover [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J : Type*} [Finite J] (Q : J → Set E) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ K.space) {ι : Type*} (U : ι → Set E)
    (hU : ∀ i, IsOpen (((↑) : K.space → E) ⁻¹' U i)) (hcover : K.space ⊆ ⋃ i, U i) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      (∀ j, (restrict R (Q j)).space = Q j) ∧
      ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ U i := by
  obtain ⟨K₀, hK₀, hfinite₀, hQ₀⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  have : Finite K₀.faces := hfinite₀.to_subtype
  have hU₀ : ∀ i, IsOpen (((↑) : K₀.space → E) ⁻¹' U i) := by
    rw [hK₀.space_eq]
    exact hU
  have hcover₀ : K₀.space ⊆ ⋃ i, U i := by rwa [hK₀.space_eq]
  obtain ⟨R, hR, hfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_cover K₀ U hU₀ hcover₀
  refine ⟨R, hR.trans hK₀, hfinite, fun j => ?_, hstars⟩
  have hsub := hR.restrict (restrict K₀ (Q j)) (restrict_faces_subset K₀ (Q j))
  rw [restrict_space_of_eq_biUnion K₀ (Q j) (hQ₀ j)] at hsub
  exact hsub.space_eq.trans (restrict_space_of_eq_biUnion K₀ (Q j) (hQ₀ j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_subcomplexes_closedStars_subset_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_subcomplexes_closedStars_subset_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_subcomplexes_closedStars_subset_cover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isSubdivision_subcomplexes_closedStars_subset_cover

end Restrict

end DifferentialGeometry.Topology.PiecewiseLinear
