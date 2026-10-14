/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSubcomplex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Classical in
theorem derivedNeighborhoodCellBase_inter_subcomplex
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ L.faces) :
    (derivedNeighborhoodCellBase K s).space ∩ L.space =
      (derivedNeighborhoodCellBase L s).space := by
  have hsub : (derivedNeighborhoodCellBase L s).space ⊆
      (derivedNeighborhoodCellBase K s).space := by
    apply space_mono_of_faces_subset
    rintro u ⟨d, hd, hne, hlt, rfl⟩
    exact ⟨d, hd.of_le (barycentricSubdivision_faces_subset hLK), hne, hlt, rfl⟩
  have hcone := coneSet_upperLink_inter_subcomplex K L hLK hs
  change coneSet (s.centroid ℝ id) (derivedNeighborhoodCellBase K s).space ∩ L.space =
    coneSet (s.centroid ℝ id) (derivedNeighborhoodCellBase L s).space at hcone
  have hrad := isConeBase_centroid_upperLink K (hLK hs)
  apply Subset.antisymm
  · rintro x ⟨hxS, hxL⟩
    have hxC : x ∈ coneSet (s.centroid ℝ id)
        (derivedNeighborhoodCellBase L s).space := by
      rw [← hcone]
      exact ⟨subset_coneSet _ _ hxS, hxL⟩
    rcases mem_coneSet_iff.mp hxC with rfl | ⟨z, hz, t, ht, -, rfl⟩
    · exact (hrad.notMem_space hxS).elim
    · have hzx := hrad.radial z (hsub hz) _ hxS t ht rfl
      rw [hzx]
      exact hz
  · intro x hx
    refine ⟨hsub hx, ?_⟩
    have hxC : x ∈ coneSet (s.centroid ℝ id)
        (derivedNeighborhoodCellBase L s).space := subset_coneSet _ _ hx
    rw [← hcone] at hxC
    exact hxC.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCellBase_inter_subcomplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCellBase_inter_subcomplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCellBase_inter_subcomplex ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.derivedNeighborhoodCellBase_inter_subcomplex

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCellBase_inter
    [FiniteDimensional ℝ E] {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hLK : L.faces ⊆ K.faces) {s : Finset E}
    (hs : s ∈ (boundaryComplex (n + 1) L).faces) :
    IsPLBall n ((derivedNeighborhoodCellBase K s).space ∩ L.space) := by
  rw [derivedNeighborhoodCellBase_inter_subcomplex K L hLK
    (boundaryComplex_faces_subset (n + 1) L hs)]
  exact hL.isPLBall_derivedNeighborhoodCellBase hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCellBase_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCellBase_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCellBase_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhoodCellBase_inter

end DifferentialGeometry.Topology.PiecewiseLinear
