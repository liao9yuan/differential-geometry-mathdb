/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerivedNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem geometricLink_eq_of_space_mem_nhdsWithin
    {K L : Geometry.SimplicialComplex ℝ E} (hLK : L.faces ⊆ K.faces) {p : E}
    (hL : L.space ∈ 𝓝[K.space] p) :
    SimplicialComplex.geometricLink L {p} = SimplicialComplex.geometricLink K {p} := by
  classical
  ext s
  simp only [SimplicialComplex.mem_geometricLink_singleton]
  constructor
  · rintro ⟨hne, hps, hs⟩
    exact ⟨hne, hps, hLK hs⟩
  · rintro ⟨hne, hps, hs⟩
    exact ⟨hne, hps, mem_faces_of_mem_nhdsWithin_space hLK hs
      (subset_convexHull ℝ _ (Finset.mem_insert_self p s)) hL⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_eq_of_space_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_eq_of_space_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_eq_of_space_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.geometricLink_eq_of_space_mem_nhdsWithin

open _root_.Classical in
theorem mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin [FiniteDimensional ℝ E]
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L) (hLK : L.space ⊆ K.space)
    {p : E} (hp : p ∈ L.space) (hnhds : L.space ∈ 𝓝[K.space] p) :
    p ∈ (boundaryComplex (n + 1) L).space ↔ p ∈ (boundaryComplex (n + 1) K).space := by
  classical
  obtain ⟨R, hR, hRfin, hpR⟩ := exists_isSubdivision_singleton_mem K (hLK hp)
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨T, hT, hTfin, hTL⟩ := exists_isSubdivision_restrict_isSubdivision R L
    (by rwa [hR.space_eq])
  let _ : Finite T.faces := hTfin.to_subtype
  let A := restrict T L.space
  let _ : Finite A.faces := (restrict_faces_finite T L.space).to_subtype
  have hpT : {p} ∈ T.faces := hT.singleton_mem hpR
  have hpA : {p} ∈ A.faces := ⟨hpT, by simpa using hp⟩
  have hnhds' : A.space ∈ 𝓝[T.space] p := by
    rw [hTL.space_eq, hT.space_eq, hR.space_eq]
    exact hnhds
  have hlink := geometricLink_eq_of_space_mem_nhdsWithin (restrict_faces_subset T L.space) hnhds'
  rw [← isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision L A hL hTL hpA,
    hlink]
  exact isPLBall_geometricLink_iff_mem_boundaryComplex_of_isSubdivision K T hK
    (hT.trans hR) hpT

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin

end DifferentialGeometry.Topology.PiecewiseLinear
