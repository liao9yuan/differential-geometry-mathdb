/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Orientation
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem frontier_preimage_glued₂_space_in_double {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) :
    frontier (((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
      (glued₂ K (boundaryComplex (n + 2) K) id).space) =
      ((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
        (simplicialMap K (glueEmbed₂ (boundaryComplex (n + 2) K) id) ''
          (boundaryComplex (n + 2) K).space) := by
  classical
  let R := boundaryRelSubdivision (n + 2) K
  let B := boundaryComplex (n + 2) K
  let A := glued₂ K B id
  let L := double (n + 2) K
  let _ : Finite R.faces := (boundaryRelSubdivision_faces_finite (n + 2) K).to_subtype
  let _ : Finite A.faces := (glued₂_faces_finite K B id).to_subtype
  let _ : Finite L.faces := (gluedComplex_faces_finite R K (isGlueIso_id B)
    (boundaryComplex_faces_subset (n + 2) K)
    (boundaryComplex_full_boundaryRelSubdivision (n + 2) K)).to_subtype
  have hL : IsCombinatorialManifold (n + 2) L :=
    isCombinatorialManifold_double_succ_succ K hK
  have hι : IsPLHomeomorphOn (simplicialMap K (glueEmbed₂ B id)) K.space A.space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hAL : A.space ⊆ L.space := by
    dsimp only [L, double]
    rw [gluedComplex_space]
    exact _root_.Set.subset_union_right
  let _ : DecidableEq (E × E × ℝ) := Classical.decEq _
  have hLB : (boundaryComplex (n + 2) L).space = ∅ := by
    change (⋃ t ∈ (boundaryComplex (n + 2) L).faces,
      convexHull ℝ (t : Set (E × E × ℝ))) = ∅
    rw [hL.boundaryComplex_faces_eq_empty]
    simp
  have hdis : Disjoint A.space (boundaryComplex (n + 2) L).space := by
    rw [hLB]
    simp
  have hfront := frontier_preimage_space_eq_preimage_boundaryComplex L A
    hL.isCombinatorialManifoldWithBoundary (hK.of_isPLHomeomorphOn hι) hAL hdis
  rw [boundaryComplex_space_of_isPLHomeomorphOn K A hK hι] at hfront
  exact hfront

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.frontier_preimage_glued₂_space_in_double then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.frontier_preimage_glued₂_space_in_double"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.frontier_preimage_glued₂_space_in_double ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.frontier_preimage_glued₂_space_in_double

open _root_.Classical in
theorem frontier_image_glued₂_space_in_double_chart {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (double (n + 2) K).space X) :
    e.target ∩ frontier (e '' (e.source ∩
      ((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
        (glued₂ K (boundaryComplex (n + 2) K) id).space)) =
      e '' (e.source ∩ ((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
        (simplicialMap K (glueEmbed₂ (boundaryComplex (n + 2) K) id) ''
          (boundaryComplex (n + 2) K).space)) := by
  let C := ((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
    (glued₂ K (boundaryComplex (n + 2) K) id).space
  have himage : e.IsImage C (e '' (e.source ∩ C)) := by
    intro x hx
    constructor
    · rintro ⟨z, ⟨hz, hzC⟩, hzx⟩
      exact e.injOn hz hx hzx ▸ hzC
    · exact fun hxC => ⟨x, ⟨hx, hxC⟩, rfl⟩
  have h := himage.frontier.image_eq.symm
  rw [show frontier C = _ from frontier_preimage_glued₂_space_in_double K hK] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.frontier_image_glued₂_space_in_double_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.frontier_image_glued₂_space_in_double_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.frontier_image_glued₂_space_in_double_chart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.frontier_image_glued₂_space_in_double_chart

open _root_.Classical in
theorem eventually_mem_frontier_image_glued₂_iff {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K)
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph (double (n + 2) K).space X)
    {y : (double (n + 2) K).space} (hy : y ∈ e.source) :
    ∀ᶠ z in 𝓝 (e y), z ∈ frontier (e '' (e.source ∩
      ((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
        (glued₂ K (boundaryComplex (n + 2) K) id).space)) ↔
      z ∈ e '' (e.source ∩ ((↑) : (double (n + 2) K).space → E × E × ℝ) ⁻¹'
        (simplicialMap K (glueEmbed₂ (boundaryComplex (n + 2) K) id) ''
          (boundaryComplex (n + 2) K).space)) := by
  filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with z hz
  rw [← frontier_image_glued₂_space_in_double_chart K hK e]
  exact (and_iff_right hz).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_frontier_image_glued₂_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_frontier_image_glued₂_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_frontier_image_glued₂_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.eventually_mem_frontier_image_glued₂_iff

end DifferentialGeometry.Topology.PiecewiseLinear
