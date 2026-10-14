/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePieceCellImage
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellIntersectionBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} (T : LocallyFinitePLPieceIn E 3 M U)

theorem LocallyFinitePLPieceIn.inter_subset_image_boundary_of_isPLBall
    {A B : Set E} {r : (Fin 4 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 4)) A) (hB : IsPLBall 3 B)
    (hAK : A ⊆ T.complex.space) (hBK : B ⊆ T.complex.space)
    (hI : IsPLBall 2 (A ∩ B)) : A ∩ B ⊆ r '' stdSimplexBoundary 3 := by
  obtain ⟨s, hs⟩ := hB
  obtain ⟨q, hq⟩ := hI
  have hCA := T.isPLCellOn_image (by decide : 3 ≤ 3) hr hAK
  have hCB := T.isPLCellOn_image (by decide : 3 ≤ 3) hs hBK
  have hCI := T.isPLCellOn_image (by decide : 2 ≤ 3) hq (inter_subset_left.trans hAK)
  rw [T.bijOn.injOn.image_inter hAK hBK] at hCI
  have hbound := hCA.inter_subset_boundary_of_isPLCellOn hCB hCI
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hbound ⟨mem_image_of_mem T.map hx.1, _root_.Set.mem_image_of_mem T.map hx.2⟩
  have hyA : y ∈ A := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact hr.bijOn.mapsTo hz.1
  exact (T.bijOn.injOn (hAK hyA) (hAK hx.1) hyx) ▸ hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_image_boundary_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_image_boundary_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_image_boundary_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_image_boundary_of_isPLBall

open _root_.Classical in
theorem LocallyFinitePLPieceIn.inter_subset_boundaryComplex_of_isPLBall
    {A B : Set E} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : K.space = A) (hA : IsPLBall 3 A) (hB : IsPLBall 3 B)
    (hAK : A ⊆ T.complex.space) (hBK : B ⊆ T.complex.space)
    (hI : IsPLBall 2 (A ∩ B)) : A ∩ B ⊆ (boundaryComplex 3 K).space := by
  classical
  obtain ⟨r, hr⟩ := hA
  have hrK : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 4)) K.space := hK.symm ▸ hr
  rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hrK,
    simplexBoundary_stdVertices_space]
  exact T.inter_subset_image_boundary_of_isPLBall hr hB hAK hBK hI

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_boundaryComplex_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_boundaryComplex_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_boundaryComplex_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.LocallyFinitePLPieceIn.inter_subset_boundaryComplex_of_isPLBall

end DifferentialGeometry.Topology.PiecewiseLinear
