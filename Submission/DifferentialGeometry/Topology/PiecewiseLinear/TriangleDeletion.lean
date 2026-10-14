/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Gluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open _root_.Classical in
def eraseTriangleComplex (K : Geometry.SimplicialComplex ℝ E) (t : Finset E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ u ∈ K.faces, u.card = 3 ∧ u ≠ t ∧ s ⊆ u ∧ s.Nonempty}
  isRelLowerSet_faces := by
    rintro s ⟨u, hu, hucard, hut, hsu, hs⟩
    exact ⟨hs, fun r hrs hr => ⟨u, hu, hucard, hut, hrs.trans hsu, hr⟩⟩
  indep hs := K.indep (K.down_closed hs.choose_spec.1 hs.choose_spec.2.2.2.1 hs.choose_spec.2.2.2.2)
  inter_subset_convexHull hs hr := K.inter_subset_convexHull
    (K.down_closed hs.choose_spec.1 hs.choose_spec.2.2.2.1 hs.choose_spec.2.2.2.2)
    (K.down_closed hr.choose_spec.1 hr.choose_spec.2.2.2.1 hr.choose_spec.2.2.2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex

open _root_.Classical in
theorem mem_eraseTriangleComplex_faces_iff
    {K : Geometry.SimplicialComplex ℝ E} {t s : Finset E} :
    s ∈ (eraseTriangleComplex K t).faces ↔
      ∃ u ∈ K.faces, u.card = 3 ∧ u ≠ t ∧ s ⊆ u ∧ s.Nonempty :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_faces_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_faces_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_faces_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_faces_iff

open _root_.Classical in
theorem eraseTriangleComplex_faces_subset
    (K : Geometry.SimplicialComplex ℝ E) (t : Finset E) :
    (eraseTriangleComplex K t).faces ⊆ K.faces := by
  rintro s ⟨u, hu, -, -, hsu, hs⟩
  exact K.down_closed hu hsu hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_subset

open _root_.Classical in
theorem eraseTriangleComplex_faces_finite
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (t : Finset E) :
    (eraseTriangleComplex K t).faces.Finite :=
  (Set.toFinite K.faces).subset (eraseTriangleComplex_faces_subset K t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_faces_finite

open _root_.Classical in
theorem mem_eraseTriangleComplex_triangle_iff
    (K : Geometry.SimplicialComplex ℝ E) (t : Finset E)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 3) {s : Finset E} (hs : s.card = 3) :
    s ∈ (eraseTriangleComplex K t).faces ↔ s ∈ K.faces ∧ s ≠ t := by
  constructor
  · rintro ⟨u, hu, hucard, hut, hsu, -⟩
    have huBound := hcard u hu
    have hsuEq : s = u := Finset.eq_of_subset_of_card_le hsu (by omega)
    subst u
    exact ⟨hu, hut⟩
  · rintro ⟨hsK, hst⟩
    exact ⟨s, hsK, hs, hst, Finset.Subset.rfl, Finset.card_pos.mp (by omega)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_triangle_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_triangle_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_triangle_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_eraseTriangleComplex_triangle_iff

open _root_.Classical in
theorem eraseTriangleComplex_space
    (K : Geometry.SimplicialComplex ℝ E) (t : Finset E) :
    (eraseTriangleComplex K t).space =
      ⋃ u ∈ {u ∈ K.faces | u.card = 3 ∧ u ≠ t}, convexHull ℝ (u : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨u, hu, hucard, hut, hsu, -⟩, hxs⟩ :=
      (eraseTriangleComplex K t).mem_space_iff.mp hx
    exact mem_iUnion₂.mpr ⟨u, ⟨hu, hucard, hut⟩,
      convexHull_mono (Finset.coe_subset.mpr hsu) hxs⟩
  · intro hx
    obtain ⟨u, ⟨hu, hucard, hut⟩, hxu⟩ := mem_iUnion₂.mp hx
    exact (eraseTriangleComplex K t).convexHull_subset_space
      ⟨u, hu, hucard, hut, Finset.Subset.rfl, K.nonempty_of_mem_faces hu⟩ hxu

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eraseTriangleComplex_space

open _root_.Classical in
theorem ncard_triangles_eraseTriangleComplex_lt
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (t : Finset E) (ht : t ∈ K.faces) (htcard : t.card = 3)
    (hcard : ∀ s ∈ K.faces, s.card ≤ 3) :
    {s ∈ (eraseTriangleComplex K t).faces | s.card = 3}.ncard <
      {s ∈ K.faces | s.card = 3}.ncard := by
  let _ : Finite (eraseTriangleComplex K t).faces :=
    (eraseTriangleComplex_faces_finite K t).to_subtype
  apply Set.ncard_lt_ncard _ ((Set.toFinite K.faces).subset (Set.sep_subset _ _))
  refine ssubset_iff_subset_ne.mpr ⟨fun s hs =>
    ⟨eraseTriangleComplex_faces_subset K t hs.1, hs.2⟩, ?_⟩
  intro heq
  have htErase : t ∈ (eraseTriangleComplex K t).faces :=
    (show t ∈ {s ∈ (eraseTriangleComplex K t).faces | s.card = 3} by
      rw [heq]
      exact ⟨ht, htcard⟩).1
  exact ((mem_eraseTriangleComplex_triangle_iff K t hcard htcard).mp htErase).2 rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.ncard_triangles_eraseTriangleComplex_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.ncard_triangles_eraseTriangleComplex_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.ncard_triangles_eraseTriangleComplex_lt ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.ncard_triangles_eraseTriangleComplex_lt

section Glue

variable [DecidableEq E] [DecidableEq F]
  {A : Geometry.SimplicialComplex ℝ E} {B : Geometry.SimplicialComplex ℝ F}
  {φ : E → F} {φ' : F → E}

theorem IsGlueIso.card_image_left (h : IsGlueIso A B φ φ')
    {s : Finset E} (hs : s ∈ A.faces) : (s.image φ).card = s.card := by
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  calc
    x = φ' (φ x) := (h.left s hs x hx).symm
    _ = φ' (φ y) := congrArg φ' hxy
    _ = y := h.left s hs y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_left ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_left

theorem IsGlueIso.card_image_right (h : IsGlueIso A B φ φ')
    {t : Finset F} (ht : t ∈ B.faces) : (t.image φ').card = t.card :=
  h.symm.card_image_left ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_right ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.card_image_right

open _root_.Classical in
theorem IsGlueIso.eraseTriangleComplex (h : IsGlueIso A B φ φ')
    {t : Finset E} (ht : t ∈ A.faces) :
    IsGlueIso (eraseTriangleComplex A t) (eraseTriangleComplex B (t.image φ)) φ φ' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro s ⟨u, hu, hucard, hut, hsu, hs⟩
    have huB := h.image₁ u hu
    refine ⟨u.image φ, huB, h.card_image_left hu ▸ hucard, ?_,
      Finset.image_mono φ hsu, hs.image φ⟩
    intro hut'
    have huBack := h.image_image_left hu
    have htBack := h.image_image_left ht
    apply hut
    rw [← huBack, ← htBack, hut']
  · rintro r ⟨u, hu, hucard, hut, hru, hr⟩
    have huA := h.image₂ u hu
    refine ⟨u.image φ', huA, h.card_image_right hu ▸ hucard, ?_,
      Finset.image_mono φ' hru, hr.image φ'⟩
    intro hut'
    apply hut
    calc
      u = (u.image φ').image φ := (h.image_image_right hu).symm
      _ = t.image φ := by rw [hut']
  · intro s hs v hv
    exact h.left s (eraseTriangleComplex_faces_subset A t hs) v hv
  · intro s hs v hv
    exact h.right s (eraseTriangleComplex_faces_subset B (t.image φ) hs) v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.eraseTriangleComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.eraseTriangleComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.eraseTriangleComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsGlueIso.eraseTriangleComplex

end Glue

end DifferentialGeometry.Topology.PiecewiseLinear
