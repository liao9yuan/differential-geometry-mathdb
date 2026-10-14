/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open _root_.Classical in
theorem exists_small_homeomorph_finite_inter
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] {m n : ℕ}
    (hK : ∀ s ∈ K.faces, s.card ≤ m + 1) (hL : ∀ t ∈ L.faces, t.card ≤ n + 1)
    (hdim : m + n ≤ Module.finrank ℝ E)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : E → E, IsPLHomeomorphOn h _root_.Set.univ _root_.Set.univ ∧
      (∀ x, _root_.Dist.dist (h x) x < ε) ∧ _root_.Set.EqOn h id Uᶜ ∧ (h '' K.space ∩ L.space).Finite := by
  obtain ⟨h, G, hh, hsmall, hfix, hGfin, hGspace, hcard⟩ :=
    exists_small_homeomorph_inter_dimension_le K L hK hL hU hKU hε
  have hGfinite : G.space.Finite := by
    apply hGfin.biUnion
    intro s hs
    have hc := hcard s hs
    have hpos := Finset.card_pos.mpr (G.nonempty_of_mem_faces hs)
    have hone : s.card = 1 := by omega
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hone
    simpa only [Finset.coe_singleton, convexHull_singleton] using _root_.Set.finite_singleton x
  exact ⟨h, hh, hsmall, hfix, hGspace ▸ hGfinite⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_small_homeomorph_finite_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_small_homeomorph_finite_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_small_homeomorph_finite_inter ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_small_homeomorph_finite_inter

end DifferentialGeometry.Topology.PiecewiseLinear
