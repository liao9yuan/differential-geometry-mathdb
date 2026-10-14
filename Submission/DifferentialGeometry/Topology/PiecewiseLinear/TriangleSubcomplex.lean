/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TriangleDeletion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FaceStarBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def triangleSubcomplexIn (K : Geometry.SimplicialComplex ℝ E) (U : Set E) :
    Geometry.SimplicialComplex ℝ E :=
  subcomplexGeneratedBy K {t | t.card = 3 ∧ convexHull ℝ (t : Set E) ⊆ U}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn

theorem triangleSubcomplexIn_faces_subset (K : Geometry.SimplicialComplex ℝ E) (U : Set E) :
    (triangleSubcomplexIn K U).faces ⊆ K.faces := subcomplexGeneratedBy_faces_subset K _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_subset

theorem triangleSubcomplexIn_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (U : Set E) : (triangleSubcomplexIn K U).faces.Finite := subcomplexGeneratedBy_faces_finite K _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_faces_finite

theorem triangleSubcomplexIn_space_subset (K : Geometry.SimplicialComplex ℝ E) (U : Set E) :
    (triangleSubcomplexIn K U).space ⊆ U := by
  rw [triangleSubcomplexIn, subcomplexGeneratedBy_space]
  exact _root_.Set.iUnion₂_subset fun t ht => ht.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_space_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_space_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_space_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.triangleSubcomplexIn_space_subset

theorem exists_face_superset_card_eq_triangleSubcomplexIn
    (K : Geometry.SimplicialComplex ℝ E) (U : Set E) {s : Finset E}
    (hs : s ∈ (triangleSubcomplexIn K U).faces) :
    ∃ t ∈ (triangleSubcomplexIn K U).faces, s ⊆ t ∧ t.card = 3 :=
  exists_face_superset_card_eq_subcomplexGeneratedBy K _ (fun _ ht => ht.2.1) hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_triangleSubcomplexIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_triangleSubcomplexIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_triangleSubcomplexIn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_triangleSubcomplexIn

theorem mem_triangleSubcomplexIn_triangle_iff
    (K : Geometry.SimplicialComplex ℝ E) (U : Set E) {s : Finset E} (hscard : s.card = 3) :
    s ∈ (triangleSubcomplexIn K U).faces ↔ s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ U := by
  change s ∈ (subcomplexGeneratedBy K _).faces ↔ _
  rw [mem_subcomplexGeneratedBy_faces_of_card K _ (fun _ ht => ht.2.1) hscard]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hscard, h.2⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleSubcomplexIn_triangle_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleSubcomplexIn_triangle_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleSubcomplexIn_triangle_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_triangleSubcomplexIn_triangle_iff

open _root_.Classical in
theorem faceStarComplex_triangleSubcomplexIn_eq
    (K : Geometry.SimplicialComplex ℝ E) (U : Set E) (s : Finset E)
    (hpure : ∀ u ∈ (faceStarComplex K s).faces,
      ∃ v ∈ (faceStarComplex K s).faces, u ⊆ v ∧ v.card = 3)
    (hU : (faceStarComplex K s).space ⊆ U) :
    faceStarComplex (triangleSubcomplexIn K U) s = faceStarComplex K s := by
  have hsub : (faceStarComplex K s).faces ⊆ (triangleSubcomplexIn K U).faces := by
    intro u hu
    obtain ⟨v, hv, huv, hvcard⟩ := hpure u hu
    exact ⟨v, ⟨hv.1, hvcard, ((faceStarComplex K s).convexHull_subset_space hv).trans hU⟩,
      huv, K.nonempty_of_mem_faces hu.1⟩
  ext u
  constructor
  · intro hu
    exact ⟨triangleSubcomplexIn_faces_subset K U hu.1,
      triangleSubcomplexIn_faces_subset K U hu.2⟩
  · intro hu
    refine ⟨hsub hu, hsub ⟨hu.2, ?_⟩⟩
    simpa only [Finset.union_assoc, Finset.union_self] using hu.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.faceStarComplex_triangleSubcomplexIn_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.faceStarComplex_triangleSubcomplexIn_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.faceStarComplex_triangleSubcomplexIn_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.faceStarComplex_triangleSubcomplexIn_eq

theorem space_eq_triangleSubcomplexIn_union
    (K : Geometry.SimplicialComplex ℝ E) (U B : Set E)
    (hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3)
    (hcover : ∀ t ∈ K.faces, t.card = 3 →
      convexHull ℝ (t : Set E) ⊆ U ∨ convexHull ℝ (t : Set E) ⊆ B) :
    K.space = (triangleSubcomplexIn K U).space ∪ (K.space ∩ B) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := K.mem_space_iff.mp hx
    obtain ⟨t, ht, hut, htcard⟩ := hpure u hu
    have hxt := convexHull_mono (Finset.coe_subset.mpr hut) hxu
    rcases hcover t ht htcard with htU | htB
    · exact Or.inl ((triangleSubcomplexIn K U).convexHull_subset_space
        ((mem_triangleSubcomplexIn_triangle_iff K U htcard).mpr ⟨ht, htU⟩) hxt)
    · exact Or.inr ⟨hx, htB hxt⟩
  · exact _root_.Set.union_subset (space_mono_of_faces_subset (triangleSubcomplexIn_faces_subset K U))
      _root_.Set.inter_subset_left

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.space_eq_triangleSubcomplexIn_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.space_eq_triangleSubcomplexIn_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.space_eq_triangleSubcomplexIn_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.space_eq_triangleSubcomplexIn_union

open _root_.Classical in
theorem eraseTriangleComplex_space_eq_triangleSubcomplexIn_union
    (K : Geometry.SimplicialComplex ℝ E) (U B : Set E)
    (hpure : ∀ u ∈ K.faces, ∃ v ∈ K.faces, u ⊆ v ∧ v.card = 3)
    (hcover : ∀ u ∈ K.faces, u.card = 3 →
      convexHull ℝ (u : Set E) ⊆ U ∨ convexHull ℝ (u : Set E) ⊆ B)
    {t : Finset E} (htB : Disjoint (convexHull ℝ (t : Set E)) B) :
    (eraseTriangleComplex K t).space =
      (eraseTriangleComplex (triangleSubcomplexIn K U) t).space ∪ (K.space ∩ B) := by
  rw [eraseTriangleComplex_space K t, eraseTriangleComplex_space (triangleSubcomplexIn K U) t]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨u, ⟨hu, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
    rcases hcover u hu hucard with huU | huB
    · exact Or.inl (mem_iUnion₂.mpr ⟨u,
        ⟨(mem_triangleSubcomplexIn_triangle_iff K U hucard).mpr ⟨hu, huU⟩, hucard, hut⟩, hxu⟩)
    · exact Or.inr ⟨K.convexHull_subset_space hu hxu, huB hxu⟩
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨u, ⟨hu, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨u, ⟨triangleSubcomplexIn_faces_subset K U hu, hucard, hut⟩, hxu⟩
    · obtain ⟨u, hu, hxu⟩ := K.mem_space_iff.mp hx.1
      obtain ⟨v, hv, huv, hvcard⟩ := hpure u hu
      have hxv := convexHull_mono (Finset.coe_subset.mpr huv) hxu
      refine mem_iUnion₂.mpr ⟨v, ⟨hv, hvcard, ?_⟩, hxv⟩
      intro hvt
      exact Set.disjoint_left.mp htB (hvt ▸ hxv) hx.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space_eq_triangleSubcomplexIn_union then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space_eq_triangleSubcomplexIn_union"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space_eq_triangleSubcomplexIn_union ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space_eq_triangleSubcomplexIn_union

end DifferentialGeometry.Topology.PiecewiseLinear
