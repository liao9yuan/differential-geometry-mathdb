/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_isPLHomeomorphInto_cells {d : ℕ}
    {P PB : Set M₁} {Q QB : Set M₂}
    (hP : IsPLCellOn d P PB) (hQ : IsPLCellOn d Q QB) :
    ∃ f : M₁ → M₂, IsPLHomeomorphInto 3 f P ∧
      f '' P = Q ∧ f '' PB = QB := by
  classical
  obtain ⟨A, r, u, hr, hu, rfl, rfl⟩ := hP
  obtain ⟨B, s, v, hs, hv, rfl, rfl⟩ := hQ
  let H := s ∘ Function.invFunOn r (stdSimplex ℝ (Fin (d + 1)))
  have hH : IsPLHomeomorphOn H A B := hr.symm.trans hs
  obtain ⟨hf, hfim⟩ := exists_isPLHomeomorphInto_of_isPLHomeomorphOn hu hv hH
  refine ⟨v ∘ H ∘ Function.invFunOn u A, hf, hfim, ?_⟩
  have hbsub : stdSimplexBoundary d ⊆ stdSimplex ℝ (Fin (d + 1)) :=
    fun _ hx => hx.1
  have hAsub : r '' stdSimplexBoundary d ⊆ A := by
    rw [← hr.image_eq]
    exact _root_.Set.image_mono hbsub
  have hrinv : Function.invFunOn r (stdSimplex ℝ (Fin (d + 1))) ''
      (r '' stdSimplexBoundary d) = stdSimplexBoundary d := by
    rw [← _root_.Set.image_comp]
    have h : _root_.Set.EqOn (Function.invFunOn r (stdSimplex ℝ (Fin (d + 1))) ∘ r)
        id (stdSimplexBoundary d) :=
      fun x hx => hr.bijOn.invOn_invFunOn.1 (hbsub hx)
    exact h.image_eq.trans (_root_.Set.image_id _)
  have huinv : Function.invFunOn u A '' (u '' (r '' stdSimplexBoundary d)) =
      r '' stdSimplexBoundary d := by
    rw [← _root_.Set.image_comp]
    have h : _root_.Set.EqOn (Function.invFunOn u A ∘ u) id (r '' stdSimplexBoundary d) :=
      fun x hx => hu.injOn.leftInvOn_invFunOn (hAsub hx)
    exact h.image_eq.trans (_root_.Set.image_id _)
  calc
    (v ∘ H ∘ Function.invFunOn u A) '' (u '' (r '' stdSimplexBoundary d))
        = v '' (H '' (Function.invFunOn u A '' (u '' (r '' stdSimplexBoundary d)))) := by
            rw [_root_.Set.image_comp, _root_.Set.image_comp]
    _ = v '' (H '' (r '' stdSimplexBoundary d)) := by rw [huinv]
    _ = v '' (s '' stdSimplexBoundary d) := by
      congr 1
      change (s ∘ Function.invFunOn r (stdSimplex ℝ (Fin (d + 1)))) ''
        (r '' stdSimplexBoundary d) = _
      rw [_root_.Set.image_comp, hrinv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_cells then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_cells"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_cells ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphInto_cells

end DifferentialGeometry.Topology.PiecewiseLinear
