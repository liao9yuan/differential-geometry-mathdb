/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CapDeletion
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldFaces
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem card_le_of_mem_boundaryComplex_faces [DecidableEq E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E}
    (hs : s ∈ (boundaryComplex n K).faces) : s.card ≤ n := by
  obtain ⟨-, t, -, hst, htn, -⟩ := (mem_boundaryComplex_faces_iff n K).mp hs
  exact (Finset.card_le_card hst).trans htn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.card_le_of_mem_boundaryComplex_faces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.card_le_of_mem_boundaryComplex_faces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.card_le_of_mem_boundaryComplex_faces ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.card_le_of_mem_boundaryComplex_faces

theorem IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space
    [FiniteDimensional ℝ E] {n : ℕ} {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K) (hLK : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ n) : K.space ⊆ closure (K.space \ L.space) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx
  obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_superset_card_eq hs
  have htL : t ∉ L.faces := by
    intro h
    have := hcard t h
    omega
  have hopen : openSimplex t ⊆ K.space \ L.space := fun y hy =>
    ⟨K.convexHull_subset_space ht (openSimplex_subset_convexHull t hy),
      notMem_space_of_notMem_faces hLK ht htL hy⟩
  refine closure_mono hopen (convexHull_subset_closure_openSimplex
    (K.nonempty_of_mem_faces ht) ?_)
  exact convexHull_mono (Finset.coe_subset.mpr hst) (openSimplex_subset_convexHull s hxs)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_space

theorem IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space
    [DecidableEq E] [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary n K) :
    K.space ⊆ closure (K.space \ (boundaryComplex n K).space) :=
  hK.space_subset_closure_sdiff_space (boundaryComplex_faces_subset n K)
    fun _ hs => card_le_of_mem_boundaryComplex_faces n K hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.space_subset_closure_sdiff_boundaryComplex_space

theorem isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary
    [FiniteDimensional ℝ E] [DecidableEq (E × ℝ)]
    (A L : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) L) (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : L.faces ⊆ A.faces) [Finite A.faces] [Finite L.faces]
    (hAm : IsCombinatorialManifoldWithBoundary 2 A) (hL : IsPLSphere 1 L.space)
    (hS : IsPLSphere 2 (capComplex A L h hA hLA).space) :
    IsPLBall 2 A.space :=
  isPLBall_space_of_isPLSphere_capComplex A L h hA hLA hL hS
    (hAm.space_subset_closure_sdiff_space hLA fun _ hs => by
      have := card_le_of_isPLSphere L hL hs
      omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_of_isCombinatorialManifoldWithBoundary

theorem isPLBall_space_of_isPLSphere_capComplex_boundaryComplex
    [FiniteDimensional ℝ E] [DecidableEq (E × ℝ)]
    (A : Geometry.SimplicialComplex ℝ (E × ℝ)) {x₀ : E}
    (h : IsConeBase ((x₀, 1) : E × ℝ) (boundaryComplex 2 A))
    (hA : ∀ q ∈ A.space, (q : E × ℝ).2 = 0)
    (hLA : (boundaryComplex 2 A).faces ⊆ A.faces) [Finite A.faces]
    [Finite (boundaryComplex 2 A).faces] (hAm : IsCombinatorialManifoldWithBoundary 2 A)
    (hL : IsPLSphere 1 (boundaryComplex 2 A).space)
    (hS : IsPLSphere 2 (capComplex A (boundaryComplex 2 A) h hA hLA).space) :
    IsPLBall 2 A.space :=
  isPLBall_space_of_isPLSphere_capComplex A (boundaryComplex 2 A) h hA hLA hL hS
    hAm.space_subset_closure_sdiff_boundaryComplex_space

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_boundaryComplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_boundaryComplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_boundaryComplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_space_of_isPLSphere_capComplex_boundaryComplex

end DifferentialGeometry.Topology.PiecewiseLinear
