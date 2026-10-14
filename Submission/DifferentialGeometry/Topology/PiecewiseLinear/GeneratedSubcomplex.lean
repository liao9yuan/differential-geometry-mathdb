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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def subcomplexGeneratedBy (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ t ∈ K.faces ∩ A, s ⊆ t ∧ s.Nonempty}
  isRelLowerSet_faces := by
    rintro s ⟨t, ht, hst, hs⟩
    exact ⟨hs, fun u hus hu => ⟨t, ht, hus.trans hst, hu⟩⟩
  indep hs := K.indep (K.down_closed hs.choose_spec.1.1 hs.choose_spec.2.1 hs.choose_spec.2.2)
  inter_subset_convexHull hs ht := K.inter_subset_convexHull
    (K.down_closed hs.choose_spec.1.1 hs.choose_spec.2.1 hs.choose_spec.2.2)
    (K.down_closed ht.choose_spec.1.1 ht.choose_spec.2.1 ht.choose_spec.2.2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy

theorem subcomplexGeneratedBy_faces_subset (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E))
    :
    (subcomplexGeneratedBy K A).faces ⊆ K.faces := by
  rintro s ⟨t, ht, hst, hs⟩
  exact K.down_closed ht.1 hst hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_subset ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_subset

theorem subcomplexGeneratedBy_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (A : Set (Finset E)) : (subcomplexGeneratedBy K A).faces.Finite :=
  (Set.toFinite K.faces).subset (subcomplexGeneratedBy_faces_subset K A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_finite ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_faces_finite

theorem subcomplexGeneratedBy_space (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) :
    (subcomplexGeneratedBy K A).space = ⋃ t ∈ K.faces ∩ A, convexHull ℝ (t : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨t, ht, hst, -⟩, hxs⟩ := (subcomplexGeneratedBy K A).mem_space_iff.mp hx
    exact mem_iUnion₂.mpr ⟨t, ht, convexHull_mono (Finset.coe_subset.mpr hst) hxs⟩
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact (subcomplexGeneratedBy K A).convexHull_subset_space
      ⟨t, ht, Finset.Subset.rfl, K.nonempty_of_mem_faces ht.1⟩ hxt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_space

theorem exists_face_superset_card_eq_subcomplexGeneratedBy
    (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) {n : ℕ}
    (hcard : ∀ t ∈ K.faces ∩ A, t.card = n) {s : Finset E}
    (hs : s ∈ (subcomplexGeneratedBy K A).faces) :
    ∃ t ∈ (subcomplexGeneratedBy K A).faces, s ⊆ t ∧ t.card = n := by
  obtain ⟨t, ht, hst, -⟩ := hs
  exact ⟨t, ⟨t, ht, Finset.Subset.rfl, K.nonempty_of_mem_faces ht.1⟩, hst, hcard t ht⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_subcomplexGeneratedBy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_subcomplexGeneratedBy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_subcomplexGeneratedBy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_face_superset_card_eq_subcomplexGeneratedBy

theorem mem_subcomplexGeneratedBy_faces_of_card
    (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) {n : ℕ}
    (hcard : ∀ t ∈ K.faces ∩ A, t.card = n) {s : Finset E} (hscard : s.card = n) :
    s ∈ (subcomplexGeneratedBy K A).faces ↔ s ∈ K.faces ∩ A := by
  constructor
  · rintro ⟨t, ht, hst, -⟩
    have heq : s = t := Finset.eq_of_subset_of_card_le hst (by rw [hcard t ht, hscard])
    exact heq.symm ▸ ht
  · intro hs
    exact ⟨s, hs, Finset.Subset.rfl, K.nonempty_of_mem_faces hs.1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_subcomplexGeneratedBy_faces_of_card then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_subcomplexGeneratedBy_faces_of_card"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_subcomplexGeneratedBy_faces_of_card ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_subcomplexGeneratedBy_faces_of_card

theorem subcomplexGeneratedBy_compl_compl (K A : Geometry.SimplicialComplex ℝ E) {n : ℕ}
    (hAK : A.faces ⊆ K.faces) (hK : ∀ t ∈ K.faces, t.card ≤ n)
    (hA : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = n) :
    subcomplexGeneratedBy K (subcomplexGeneratedBy K A.facesᶜ).facesᶜ = A := by
  classical
  ext s
  constructor
  · rintro ⟨t, ⟨htK, htR⟩, hst, hs⟩
    have htA : t ∈ A.faces := by
      by_contra ht
      exact htR ⟨t, ⟨htK, ht⟩, Finset.Subset.rfl, K.nonempty_of_mem_faces htK⟩
    exact A.down_closed htA hst hs
  · intro hs
    obtain ⟨t, ht, hst, htcard⟩ := hA s hs
    refine ⟨t, ⟨hAK ht, ?_⟩, hst, A.nonempty_of_mem_faces hs⟩
    rintro ⟨u, ⟨huK, huA⟩, htu, _⟩
    have heq : t = u := Finset.eq_of_subset_of_card_le htu (by rw [htcard]; exact hK u huK)
    exact huA (heq ▸ ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_compl_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_compl_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_compl_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.subcomplexGeneratedBy_compl_compl

end DifferentialGeometry.Topology.PiecewiseLinear
