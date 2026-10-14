/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundarySphere
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.isPolyhedralBall {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {d : ℕ} {C B : Set M} (hC : IsPLCellOn d C B) : IsPolyhedralBall (n := 3) d C := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := hC
  have hP : IsPLBall d P := ⟨r, hr⟩
  obtain ⟨T, -, hTP⟩ := hu.exists_pLPiece_of_isPolyhedron hP.isPolyhedron
  exact ⟨⟨3, T⟩, hTP.symm ▸ hP⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedralBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedralBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedralBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLCellOn.isPolyhedralBall

theorem IsPolyhedralBall.exists_isPLCellOn {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {d : ℕ} {C : Set M} (hC : IsPolyhedralBall (n := 3) d C) (hd : d ≤ 3) :
    ∃ B : Set M, IsPLCellOn d C B := by
  obtain ⟨-, -, ⟨P, r, -, hr, -, -, -⟩, -⟩ := exists_isPLCellOn_of_le_three d hd
  obtain ⟨T, q, hq⟩ := hC
  have hP : IsPLBall d P := ⟨r, hr⟩
  have hf := hr.symm.trans hq
  have hpl := T.piece.isPLOn_comp hf.isPiecewiseAffineOn hf.bijOn.mapsTo
  have hinj := T.piece.bijOn.injOn.comp hf.bijOn.injOn hf.bijOn.mapsTo
  have hu := hpl.isPLHomeomorphInto hP.isPolyhedron.isCompact hinj
  refine ⟨(T.piece.map ∘ (q ∘ Function.invFunOn r _)) '' (r '' stdSimplexBoundary d),
    P, r, T.piece.map ∘ (q ∘ Function.invFunOn r _), hr, hu, ?_, rfl⟩
  rw [_root_.Set.image_comp, hf.image_eq, T.piece.bijOn.image_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.exists_isPLCellOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.exists_isPLCellOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.exists_isPLCellOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.exists_isPLCellOn

theorem IsPolyhedralBall.isPLCellOn {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C : Set M} (hC : IsPolyhedralBall (n := 3) 3 C) :
    IsPLCellOn 3 C (frontier C) := by
  obtain ⟨B, hB⟩ := hC.exists_isPLCellOn le_rfl
  exact hB.boundary_eq_frontier ▸ hB

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLCellOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLCellOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLCellOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPolyhedralBall.isPLCellOn

end DifferentialGeometry.Topology.PiecewiseLinear
