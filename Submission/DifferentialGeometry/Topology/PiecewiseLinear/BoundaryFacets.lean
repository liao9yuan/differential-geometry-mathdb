/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface
    [dE : DecidableEq E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E}
    (hcard : s.card = n + 1) :
    s ∈ (boundaryComplex (n + 1) K).faces ↔
      ∃ a, {w | w ∉ s ∧ _root_.Insert.insert w s ∈ K.faces} = {a} := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  constructor
  · intro hs
    have hlink := ((hK.mem_boundaryComplex_faces_iff K).mp hs).2.2
    rw [hcard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le K s hbound] at hlink
    exact isPLBall_zero_iff.mp hlink
  · rintro ⟨a, ha⟩
    have hamem : a ∉ s ∧ _root_.Insert.insert a s ∈ K.faces := by
      change a ∈ {w | w ∉ s ∧ _root_.Insert.insert w s ∈ K.faces}
      rw [ha]
      exact _root_.Set.mem_singleton a
    have hs : s ∈ K.faces := K.down_closed hamem.2 (Finset.subset_insert a s)
      (Finset.card_pos.mp (by omega))
    apply (hK.mem_boundaryComplex_faces_iff K).mpr
    refine ⟨hs, hcard.le, ?_⟩
    rw [hcard, Nat.sub_self, geometricLink_space_eq_coface_vertices_of_card_le K s hbound]
    exact isPLBall_zero_iff.mpr ⟨a, ha⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface

theorem boundaryComplex_eq_subcomplexGeneratedBy_facets [DecidableEq E] {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall (n + 1) K.space) :
    boundaryComplex (n + 1) K = subcomplexGeneratedBy (boundaryComplex (n + 1) K)
      {s | s.card = n + 1} := by
  have hfin : Finite (boundaryComplex (n + 1) K).faces :=
    (boundaryComplex_faces_finite (n + 1) K).to_subtype
  have hB := isPLSphere_boundaryComplex_space_of_isPLBall (n := n) K hK
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, hst, hcard⟩ :=
      exists_face_superset_card_eq_of_isPLSphere (boundaryComplex (n + 1) K) hB hs
    exact ⟨t, ⟨ht, hcard⟩, hst, (boundaryComplex (n + 1) K).nonempty_of_mem_faces hs⟩
  · intro hs
    exact subcomplexGeneratedBy_faces_subset (boundaryComplex (n + 1) K) {t | t.card = n + 1} hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_eq_subcomplexGeneratedBy_facets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_eq_subcomplexGeneratedBy_facets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_eq_subcomplexGeneratedBy_facets ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.boundaryComplex_eq_subcomplexGeneratedBy_facets

end DifferentialGeometry.Topology.PiecewiseLinear
