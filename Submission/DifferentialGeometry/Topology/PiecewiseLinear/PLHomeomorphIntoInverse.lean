/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Transition361

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [Nonempty M]

theorem IsPLHomeomorphInto.invFunOn {f : M → N} {P : Set M}
    (hf : IsPLHomeomorphInto n f P) :
    IsPLHomeomorphInto n (Function.invFunOn f P) (f '' P) := by
  have hi := hf.injOn.bijOn_image.invOn_invFunOn
  have hbij : _root_.Set.BijOn (Function.invFunOn f P) (f '' P) P := hi.symm.bijOn
    hf.injOn.bijOn_image.surjOn.mapsTo_invFunOn hf.injOn.bijOn_image.mapsTo
  refine ⟨hf.isPLOn_inverse hi.1, hbij.injOn, ?_⟩
  intro y hy
  refine ⟨f, ?_, hi.2⟩
  rw [hbij.image_eq] at hy ⊢
  exact hf.isPLOn y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.invFunOn

end DifferentialGeometry.Topology.PiecewiseLinear
