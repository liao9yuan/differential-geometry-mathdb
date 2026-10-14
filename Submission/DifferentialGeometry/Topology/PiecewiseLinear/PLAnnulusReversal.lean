/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLAnnulusEnds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.symm {C J₀ J₁ : Set E3}
    (h : IsPLAnnulusWithEnds C J₀ J₁) : IsPLAnnulusWithEnds C J₁ J₀ := by
  have hflip : IsPLHomeomorphOn (fun t : ℝ => 1 - t) (_root_.Set.Icc 0 1) (_root_.Set.Icc 0 1) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (AffineMap.const ℝ ℝ 1 - AffineMap.id ℝ ℝ) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]
    · intro t _ u _ heq
      linarith
    · intro t ht
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      ring
  obtain ⟨J, ρ, hJ, hρ, h₀, h₁⟩ := h
  refine ⟨J, ρ ∘ Prod.map id (fun t : ℝ => 1 - t), hJ,
    (hJ.isPolyhedron.isPLHomeomorphOn_id.prodMap hflip).trans hρ, ?_, ?_⟩
  · rw [_root_.Set.image_comp, _root_.Set.prodMap_image_prod, _root_.Set.image_id, _root_.Set.image_singleton, sub_zero, ← h₁]
  · rw [_root_.Set.image_comp, _root_.Set.prodMap_image_prod, _root_.Set.image_id, _root_.Set.image_singleton, sub_self, ← h₀]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.symm ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLAnnulusWithEnds.symm

end DifferentialGeometry.Topology.PiecewiseLinear
