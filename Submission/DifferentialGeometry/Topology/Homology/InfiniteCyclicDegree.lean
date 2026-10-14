/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import Mathlib.Algebra.Group.Int.Units

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace DifferentialGeometry.Topology

universe u

theorem integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (f : C(X, Y))
    (hf : Function.Surjective (integralSingularHomologyMap n f))
    (eX : integralSingularHomology n X ≃ₗ[ℤ] ℤ)
    (eY : integralSingularHomology n Y ≃ₗ[ℤ] ℤ) :
    eY (integralSingularHomologyMap n f (eX.symm 1)) = 1 ∨
      eY (integralSingularHomologyMap n f (eX.symm 1)) = -1 := by
  let g : ℤ →ₗ[ℤ] ℤ :=
    eY.toLinearMap.comp ((integralSingularHomologyMap n f).comp eX.symm.toLinearMap)
  have hg : Function.Surjective g := eY.surjective.comp (hf.comp eX.symm.surjective)
  obtain ⟨z, hz⟩ := hg 1
  have hmul : z * g 1 = 1 := by
    calc
      z * g 1 = g (z • (1 : ℤ)) := by rw [map_smul]; rfl
      _ = 1 := by simpa using hz
  exact (Int.eq_one_or_neg_one_of_mul_eq_one' hmul).imp And.right And.right

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective

end DifferentialGeometry.Topology
