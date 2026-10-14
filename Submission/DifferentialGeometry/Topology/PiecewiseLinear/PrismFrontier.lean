/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
theorem IsPLHomeomorphOn.frontier_prism_image
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {a b : ℝ} (hab : a < b) {f : E × ℝ → F} {S : Set F}
    (hf : IsPLHomeomorphOn f (D.space ×ˢ _root_.Set.Icc a b) S)
    (hdim : Module.finrank ℝ F = 3) :
    frontier S = f '' (D.space ×ˢ {a, b} ∪ (boundaryComplex 2 D).space ×ˢ _root_.Set.Icc a b) := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  have hprism := isPLBall_three_prod hD (isPLBall_Icc hab)
  obtain ⟨Q, hQfin, hQsp⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 3 Q.space := hQsp.symm ▸ hprism
  have hS := hprism.of_isPLHomeomorphOn hf
  obtain ⟨K, hKfin, hKsp⟩ := hS.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 3 K.space := hKsp.symm ▸ hS
  have hmap : IsPLHomeomorphOn f Q.space K.space := by rw [hQsp, hKsp]; exact hf
  rw [← hKsp, frontier_space_eq_boundaryComplex_space_of_finrank hdim K
    hK.isCombinatorialManifoldWithBoundary,
    boundaryComplex_space_of_isPLHomeomorphOn Q K hQ.isCombinatorialManifoldWithBoundary hmap,
    boundaryComplex_space_prism D hD hab Q hQsp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.frontier_prism_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.frontier_prism_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.frontier_prism_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphOn.frontier_prism_image

end DifferentialGeometry.Topology.PiecewiseLinear
