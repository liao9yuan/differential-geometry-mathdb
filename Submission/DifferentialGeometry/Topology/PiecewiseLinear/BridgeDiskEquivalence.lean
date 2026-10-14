/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskBoundaryCollar
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BridgeCollarEquivalence
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SphericalArcChartMatching

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsBridgeDisk.exists_isPLHomeomorphOn_map_arc
    {C A B D A' B' : Set E3} {a b a' b' : E3}
    (h : IsBridgeDisk C A B a b) (h' : IsBridgeDisk D A' B' a' b')
    (hC : IsPLBall 3 C) (hD : IsPLBall 3 D) :
    ∃ G : E3 → E3, IsPLHomeomorphOn G C D ∧ G '' A = A' ∧ G a = a' ∧ G b = b' := by
  obtain ⟨Φ, N, Ω, τ, hN, -, hΦ, hτ, hcore, hβ, ha, hb, -, hΦF, -, -, -⟩ :=
    h.exists_arcPatternChart (by simp) hC
  obtain ⟨Φ', N', Ω', τ', hN', -, hΦ', hτ', hcore', hβ', ha', hb', -, hΦF', -, -, -⟩ :=
    h'.exists_arcPatternChart (by simp) hD
  obtain ⟨f, hf, hfβ, hfa, hfb, -⟩ := exists_isPLHomeomorphOn_spheres_eq_on_charted_arc
    hC.isPLSphere_frontier hD.isPLSphere_frontier hN hN' hΦ hΦ' hτ hτ' hcore hcore'
    (fun p hp hz => (hΦF p hp).mpr hz) (fun p hp hz => (hΦF' p hp).mpr hz)
  rw [hβ, hβ'] at hfβ
  rw [ha, ha'] at hfa
  rw [hb, hb'] at hfb
  obtain ⟨W, c, -, hWC, -, hc, hc0, -, hcB, -⟩ := h.exists_boundary_collar (by simp) hC
  obtain ⟨Z, d, -, hZD, -, hd, hd0, -, hdB, -⟩ := h'.exists_boundary_collar (by simp) hD
  obtain ⟨G, hG, hGf, hGA⟩ := exists_isPLHomeomorphOn_eqOn_boundary_map_bridge_arc_of_collars
    hC hD h h' hc hd hWC hZD hc0 hd0 hcB hdB hf hfβ
  exact ⟨G, hG, hGA, (hGf (h.inter_frontier.symm.subset (Or.inl rfl)).2).trans hfa,
    (hGf (h.inter_frontier.symm.subset (Or.inr rfl)).2).trans hfb⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_map_arc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_map_arc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_map_arc ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsBridgeDisk.exists_isPLHomeomorphOn_map_arc

end DifferentialGeometry.Topology.PiecewiseLinear
