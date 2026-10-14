/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BallInterior

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLBall.isConnected_interior_of_finrank {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {P : Set E} (hP : IsPLBall (n + 1) P) :
    IsConnected (interior P) := by
  classical
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall (n + 1) K.space := hKP.symm ▸ hP
  have hKM := hK.isCombinatorialManifoldWithBoundary
  obtain ⟨f, hf⟩ := hK
  have hboundary : f '' stdSimplexBoundary (n + 1) = frontier K.space := by
    rw [frontier_space_eq_boundaryComplex_space_of_finrank hdim K hKM,
      boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hf,
      simplexBoundary_stdVertices_space]
  have hconn := hf.isConnected_sdiff_image_stdSimplexBoundary
  rw [hboundary, (isPolyhedron_space K).isClosed.frontier_eq,
    _root_.Set.sdiff_sdiff_cancel_left interior_subset, hKP] at hconn
  exact hconn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_interior_of_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_interior_of_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_interior_of_finrank ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.isConnected_interior_of_finrank

theorem IsPLBall.closure_interior_of_finrank {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 1) {P : Set E} (hP : IsPLBall (n + 1) P) :
    closure (interior P) = P := by
  let e : E ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hdim)
  have hpl : IsPiecewiseAffineOn e P :=
    (isPiecewiseAffineOn_of_affine e.toLinearMap.toAffineMap isOpen_univ).mono_of_isPolyhedron
      hP.isPolyhedron (_root_.Set.subset_univ _)
  have he : IsPLHomeomorphOn e P (e '' P) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hP.isPolyhedron hpl
      e.injective.injOn.bijOn_image
  have hball : IsPLBall (n + 1) (e '' P) := hP.of_isPLHomeomorphOn he
  apply e.injective.image_injective
  change e.toContinuousLinearEquiv.toHomeomorph '' closure (interior P) = e '' P
  rw [e.toContinuousLinearEquiv.toHomeomorph.image_closure,
    e.toContinuousLinearEquiv.toHomeomorph.image_interior]
  exact hball.closure_interior

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.closure_interior_of_finrank then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.closure_interior_of_finrank"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.closure_interior_of_finrank ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLBall.closure_interior_of_finrank

end DifferentialGeometry.Topology.PiecewiseLinear
