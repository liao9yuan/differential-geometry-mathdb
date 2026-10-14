/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeArcShrinking

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsBridgeDisk.exists_isPLHomeomorphOn_to_collar_ribbon
    {C A B W : Set E} {a b : E} (h : IsBridgeDisk C A B a b) (hC : IsPolyhedron C)
    {c : E × ℝ → E} (hc : IsPLHomeomorphOn c (frontier C ×ˢ _root_.Set.Icc (0 : ℝ) 2) W)
    (hc0 : ∀ x ∈ frontier C, c (x, 0) = x)
    (htrace : B ∩ W = c '' ((B ∩ frontier C) ×ˢ _root_.Set.Icc (0 : ℝ) 2)) :
    ∃ e : E ≃ₜ E, IsPLHomeomorphOn e _root_.Set.univ _root_.Set.univ ∧ _root_.Set.EqOn e id Cᶜ ∧
      _root_.Set.EqOn e id (frontier C) ∧ e '' C = C ∧
      IsBridgeDisk C (e '' A) (c '' ((B ∩ frontier C) ×ˢ _root_.Set.Icc (0 : ℝ) 1)) a b := by
  have hβ := h.isPLBall_inter_frontier
  have hI : IsPLBall 1 (_root_.Set.Icc (0 : ℝ) 1) := isPLBall_Icc zero_lt_one
  have hsub : (B ∩ frontier C) ×ˢ _root_.Set.Icc (0 : ℝ) 1 ⊆
      frontier C ×ˢ _root_.Set.Icc (0 : ℝ) 2 :=
    _root_.Set.prod_mono _root_.Set.inter_subset_right (fun _ ht => ⟨ht.1, ht.2.trans (by norm_num)⟩)
  have hcR := hc.restrict (hβ.isPolyhedron.prod hI.isPolyhedron) hsub
  have hR : IsPLBall 2 (c '' ((B ∩ frontier C) ×ˢ _root_.Set.Icc (0 : ℝ) 1)) :=
    (isPLBall_two_prod hβ hI).of_isPLHomeomorphOn hcR
  have hRB : c '' ((B ∩ frontier C) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ⊆ B := by
    apply Subset.trans _ (htrace.symm.subset.trans _root_.Set.inter_subset_left)
    exact _root_.Set.image_mono (_root_.Set.prod_mono subset_rfl
      (fun _ ht => ⟨ht.1, ht.2.trans (by norm_num)⟩))
  have hβR : B ∩ frontier C ⊆ c '' ((B ∩ frontier C) ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact ⟨(x, 0), ⟨hx, by norm_num⟩, hc0 x hx.2⟩
  exact h.exists_isPLHomeomorphOn_to_subdisk hC hR hRB hβR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_to_collar_ribbon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_to_collar_ribbon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_to_collar_ribbon ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_to_collar_ribbon

end DifferentialGeometry.Topology.PiecewiseLinear
