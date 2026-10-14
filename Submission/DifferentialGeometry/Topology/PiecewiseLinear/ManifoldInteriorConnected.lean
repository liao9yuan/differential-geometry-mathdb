/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.Dense
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInteriorDensity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.isPreconnected_sdiff_boundaryComplex_space
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hconn : IsPreconnected K.space) :
    IsPreconnected (K.space \ (boundaryComplex (n + 1) K).space) := by
  let I := K.space \ (boundaryComplex (n + 1) K).space
  let _ : PreconnectedSpace K.space := Subtype.preconnectedSpace hconn
  have hdense : Dense (((↑) : K.space → E) ⁻¹' I) := by
    intro x
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, inter_eq_right.mpr _root_.Set.sdiff_subset]
    exact hK.space_subset_closure_sdiff_boundaryComplex_space x.property
  have hlocal : ∀ x : K.space, ∃ V ∈ 𝓝 x,
      IsPreconnected (V ∩ ((↑) : K.space → E) ⁻¹' I) := by
    intro x
    obtain ⟨C, hC, hCK', hCnhds⟩ :=
      hK.exists_isPLBall_subset_of_mem_nhdsWithin x.property (U := _root_.Set.univ) Filter.univ_mem
    have hCK : C ⊆ K.space := hCK'.trans _root_.Set.inter_subset_left
    obtain ⟨L, hLfinite, hLC⟩ := hC.isPolyhedron.exists_simplicialComplex
    let _ : Finite L.faces := hLfinite.to_subtype
    have hL : IsPLBall (n + 1) L.space := hLC.symm ▸ hC
    obtain ⟨q, hq⟩ := hC
    have hboundary : (boundaryComplex (n + 1) L).space = q '' stdSimplexBoundary (n + 1) := by
      rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L (hLC.symm ▸ hq),
        simplexBoundary_stdVertices_space]
    have hcore : C \ q '' stdSimplexBoundary (n + 1) ⊆ C ∩ I := by
      rintro y ⟨hyC, hybd⟩
      refine ⟨hyC, hCK hyC, fun hyKbd => hybd ?_⟩
      rw [← hboundary]
      exact inter_boundaryComplex_space_subset_of_subset K L hK
        hL.isCombinatorialManifoldWithBoundary (hLC.subset.trans hCK)
          ⟨hLC.symm.subset hyC, hyKbd⟩
    have hCI : IsPreconnected (C ∩ I) :=
      hq.isConnected_sdiff_image_stdSimplexBoundary.isPreconnected.subset_closure hcore
        (hq.closure_sdiff_image_stdSimplexBoundary.symm ▸ _root_.Set.inter_subset_left)
    refine ⟨((↑) : K.space → E) ⁻¹' C,
      preimage_coe_mem_nhds_subtype.mpr hCnhds, ?_⟩
    rw [← _root_.Set.preimage_inter]
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr (inter_subset_left.trans hCK)]
  have h := DifferentialGeometry.Topology.isPreconnected_of_dense_of_locally_preconnected_inter
    hdense hlocal
  have himage := h.image ((↑) : K.space → E) continuous_subtype_val.continuousOn
  rwa [Subtype.image_preimage_coe, inter_eq_right.mpr _root_.Set.sdiff_subset] at himage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPreconnected_sdiff_boundaryComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPreconnected_sdiff_boundaryComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPreconnected_sdiff_boundaryComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isPreconnected_sdiff_boundaryComplex_space

open _root_.Classical in
theorem IsCombinatorialManifoldWithBoundary.isConnected_sdiff_boundaryComplex_space
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) (hconn : IsConnected K.space) :
    IsConnected (K.space \ (boundaryComplex (n + 1) K).space) := by
  refine ⟨?_, hK.isPreconnected_sdiff_boundaryComplex_space hconn.isPreconnected⟩
  exact closure_nonempty_iff.mp
    (hconn.nonempty.mono hK.space_subset_closure_sdiff_boundaryComplex_space)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isConnected_sdiff_boundaryComplex_space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isConnected_sdiff_boundaryComplex_space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isConnected_sdiff_boundaryComplex_space ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldWithBoundary.isConnected_sdiff_boundaryComplex_space

end DifferentialGeometry.Topology.PiecewiseLinear
