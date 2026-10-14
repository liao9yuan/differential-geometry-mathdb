/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem PLPieceIn.frontier_image_of_isPLBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X]
    {W : Set X} (T : PLPieceIn E (n + 1) X W) (hdim : Module.finrank ℝ E = n + 1)
    {A : Set E} (hA : IsPLBall (n + 1) A) (hAT : A ⊆ T.complex.space) :
    frontier (T.map '' A) = T.map '' frontier A := by
  classical
  obtain ⟨S, hSA, hST⟩ := T.exists_restrict_of_isPolyhedron hA.isPolyhedron hAT
  let : Finite S.complex.faces := S.finite_faces.to_subtype
  have hS : IsPLBall (n + 1) S.complex.space := hSA.symm ▸ hA
  rw [S.frontier_eq_image_boundaryComplex hS.isCombinatorialManifoldWithBoundary,
    ← frontier_space_eq_boundaryComplex_space_of_finrank hdim S.complex
      hS.isCombinatorialManifoldWithBoundary, hSA, hST]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.frontier_image_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.frontier_image_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.frontier_image_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.frontier_image_of_isPLBall

theorem PLPieceIn.image_interior_of_isPLBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ} {X : Type*}
    [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X]
    {W : Set X} (T : PLPieceIn E (n + 1) X W) (hdim : Module.finrank ℝ E = n + 1)
    {A : Set E} (hA : IsPLBall (n + 1) A) (hAT : A ⊆ T.complex.space) :
    T.map '' interior A = interior (T.map '' A) := by
  rw [← self_sdiff_frontier A,
    (T.bijOn.injOn.mono hAT).image_sdiff_subset hA.isPolyhedron.isClosed.frontier_subset,
    ← T.frontier_image_of_isPLBall hdim hA hAT, self_sdiff_frontier]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.image_interior_of_isPLBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.image_interior_of_isPLBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.image_interior_of_isPLBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLPieceIn.image_interior_of_isPLBall

end DifferentialGeometry.Topology.PiecewiseLinear
