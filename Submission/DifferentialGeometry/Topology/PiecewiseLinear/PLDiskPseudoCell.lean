/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellInteriorOpen
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CellGluingSphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.isPseudoCell_of_mem_interior
    {Δ : Set (EuclideanSpace ℝ (Fin 3))}
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    {P : EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ)
    (hP : P ∈ Δ \ r '' stdSimplexBoundary 2) :
    IsPseudoCell Δ (Δ \ r '' stdSimplexBoundary 2)
      (r '' stdSimplexBoundary 2) P := by
  let R : Set (EuclideanSpace ℝ (Fin 3)) := r '' stdSimplexBoundary 2
  have hRΔ : R ⊆ Δ := by
    rintro y ⟨q, hq, rfl⟩
    exact hr.bijOn.mapsTo hq.1
  have hcarrier : Δ = (Δ \ R) ∪ R := by
    ext x
    constructor
    · intro hx
      by_cases hxr : x ∈ R
      · exact Or.inr hxr
      · exact Or.inl ⟨hx, hxr⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hRΔ hx
  have hboundary : Δ \ (Δ \ R) = R := by
    ext x
    constructor
    · rintro ⟨hxΔ, hnot⟩
      by_contra hxR
      exact hnot ⟨hxΔ, hxR⟩
    · intro hxR
      exact ⟨hRΔ hxR, fun hx => hx.2 hxR⟩
  have hcell : IsTopologicalCellWithInterior 2 Δ (Δ \ R) :=
    hr.isTopologicalCellWithInterior
  have hRclosed : IsClosed R :=
    hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron.isCompact.isClosed
  have hΔ : IsPLBall 2 Δ := ⟨r, hr⟩
  refine ⟨hcarrier, hcell.isOpenTopologicalCell, ?_, ?_, ?_, hP, ?_⟩
  · change IsTopologicalSphere 1 R
    rw [← hboundary]
    exact hcell.isTopologicalSphere_boundary
  · exact disjoint_sdiff_self_left
  · calc
      closure (Δ \ R) = Δ := hr.closure_sdiff_image_stdSimplexBoundary
      _ = (Δ \ R) ∪ R := hcarrier
  · exact (hΔ.isPolyhedron.isLocallyPolyhedral.sdiff_isClosed
      hRclosed).sdiff_isClosed isClosed_singleton

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPseudoCell_of_mem_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPseudoCell_of_mem_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPseudoCell_of_mem_interior ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.isPseudoCell_of_mem_interior

end DifferentialGeometry.Topology.PiecewiseLinear
