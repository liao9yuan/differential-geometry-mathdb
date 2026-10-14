/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellNeighborhoodDisk
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellTransverseBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_generalPosition_ball_pseudoCell {Ec Eint Ebd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Bl Dc Dcint : Set E3, IsPLBall 3 Bl ∧ Bl ⊆ Metric.ball P δ ∧ P ∈ interior Bl ∧
      IsTopologicalCellWithInterior 2 Dc Dcint ∧ Dc ⊆ Eint ∧ Dc ⊆ Metric.ball P δ ∧
      P ∈ Dcint ∧ Bl ∩ Ec ⊆ Dc ∧ CrossesPseudoCell (frontier Bl) Ec Eint P := by
  obtain ⟨Dc, Dcint, hDc, hDcE, hDcδ, hPDc, ε, hε, hεD⟩ :=
    hE.exists_neighborhood_subdisk hδ
  obtain ⟨Bl, hBl, hBlδ, hPBl, hcross⟩ :=
    hE.exists_small_transverse_ball (lt_min hδ hε)
  refine ⟨Bl, Dc, Dcint, hBl,
    hBlδ.trans (Metric.ball_subset_ball (min_le_left δ ε)), hPBl,
    hDc, hDcE, hDcδ, hPDc, ?_, hcross⟩
  exact (_root_.Set.inter_subset_inter_left Ec
    (hBlδ.trans (Metric.ball_subset_ball (min_le_right δ ε)))).trans hεD

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_generalPosition_ball_pseudoCell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_generalPosition_ball_pseudoCell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_generalPosition_ball_pseudoCell ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_generalPosition_ball_pseudoCell

end DifferentialGeometry.Topology.PiecewiseLinear
