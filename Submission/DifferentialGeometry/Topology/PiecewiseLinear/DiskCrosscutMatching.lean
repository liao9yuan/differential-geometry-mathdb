/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.RectangleCrosscutCoordinates

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_disk_eq_on_crosscut
    {D A : Set E} {D' A' : Set F}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    {η : ℝ → E} (hη : IsPLHomeomorphOn η (_root_.Set.Icc 0 1) A) (hAD : A ⊆ D)
    (hmeet : A ∩ (r '' stdSimplexBoundary 2) = {η 0, η 1})
    {r' : (Fin 3 → ℝ) → F} (hr' : IsPLHomeomorphOn r' (stdSimplex ℝ (Fin 3)) D')
    {η' : ℝ → F} (hη' : IsPLHomeomorphOn η' (_root_.Set.Icc 0 1) A') (hAD' : A' ⊆ D')
    (hmeet' : A' ∩ (r' '' stdSimplexBoundary 2) = {η' 0, η' 1}) :
    ∃ f : E → F, IsPLHomeomorphOn f D D' ∧ f '' A = A' ∧
      ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, f (η t) = η' t := by
  obtain ⟨g, hg, hgη⟩ :=
    exists_isPLHomeomorphOn_rectangle_eq_on_crosscut hr hη hAD hmeet
  obtain ⟨g', hg', hgη'⟩ :=
    exists_isPLHomeomorphOn_rectangle_eq_on_crosscut hr' hη' hAD' hmeet'
  let P := _root_.Set.Icc (0 : ℝ) 1 ×ˢ _root_.Set.Icc (-1 : ℝ) 1
  let v := Function.invFunOn g P
  let f := g' ∘ v
  have hleft : ∀ z ∈ P, v (g z) = z := fun _ hz => hg.bijOn.invOn_invFunOn.1 hz
  have heq : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, f (η t) = η' t := by
    intro t ht
    change g' (v (η t)) = η' t
    rw [← hgη t ht, hleft (t, 0) ⟨ht, by norm_num⟩, hgη' t ht]
  refine ⟨f, hg.symm.trans hg', ?_, heq⟩
  rw [← hη.image_eq, _root_.Set.image_image]
  exact (show _root_.Set.EqOn (f ∘ η) η' (_root_.Set.Icc (0 : ℝ) 1) from heq).image_eq.trans hη'.image_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_disk_eq_on_crosscut then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_disk_eq_on_crosscut"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_disk_eq_on_crosscut ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_isPLHomeomorphOn_disk_eq_on_crosscut

end DifferentialGeometry.Topology.PiecewiseLinear
