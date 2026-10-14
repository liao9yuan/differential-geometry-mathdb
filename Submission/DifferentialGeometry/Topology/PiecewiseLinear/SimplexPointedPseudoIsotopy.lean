/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PointedPseudoIsotopy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.HeightTriangleStability
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.StandardTriangleCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_stdCenter
    {u : (Fin 3 → ℝ) → Fin 3 → ℝ}
    (hiso : IsPLPseudoIsotopicToId u (stdSimplex ℝ (Fin 3)))
    (hu : u (stdCenter 1) = stdCenter 1) :
    ∃ Ψ : (Fin 3 → ℝ) × ℝ → (Fin 3 → ℝ) × ℝ,
      IsPLHomeomorphOn Ψ (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1)
        (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), Ψ (x, 0) = (x, 0)) ∧
      (∀ x ∈ stdSimplex ℝ (Fin 3), Ψ (x, 1) = (u x, 1)) ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, Ψ (stdCenter 1, t) = (stdCenter 1, t) := by
  let π : (Fin 3 → ℝ) → ℝ × ℝ := fun x => (x 1, x 2)
  let Q : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
  have hQ : IsHPolytope Q := isHPolytope_coordinate_triangle
  have hπ : IsPLHomeomorphOn π (stdSimplex ℝ (Fin 3)) Q :=
    isPLHomeomorphOn_triangle_coordinate_projection
  have hc : π (stdCenter 1) ∈ interior Q := stdCenter_mem_interior_coordinate_triangle
  have hp : stdCenter 1 ∈ stdSimplex ℝ (Fin 3) :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
  have hwc : Function.invFunOn π (stdSimplex ℝ (Fin 3)) (π (stdCenter 1)) =
      stdCenter 1 := hπ.bijOn.invOn_invFunOn.1 hp
  obtain ⟨Ψ, hΨ, hΨ0, hΨ1, hΨc⟩ :=
    hiso.exists_isPLHomeomorphOn_fixed_axis_of_convex_model hQ hπ.symm hc
      (by rw [hwc]; exact hu)
  rw [hwc] at hΨc
  exact ⟨Ψ, hΨ, hΨ0, hΨ1, hΨc⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_stdCenter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_stdCenter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_stdCenter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLPseudoIsotopicToId.exists_isPLHomeomorphOn_fixed_stdCenter

end DifferentialGeometry.Topology.PiecewiseLinear
