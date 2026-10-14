/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.Connected.BallComplement

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric

namespace DifferentialGeometry.Topology

theorem IsCompact.exists_not_isBounded_connectedComponentIn_compl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hd : 1 < Module.rank ℝ E) :
    ∃ x ∉ K, ¬ Bornology.IsBounded (connectedComponentIn Kᶜ x) := by
  let _ : Nontrivial E := rank_pos_iff_nontrivial.mp (lt_trans zero_lt_one hd)
  obtain ⟨r, hKr⟩ := (_root_.Metric.isBounded_iff_subset_closedBall (0 : E)).mp hK.isBounded
  have hconn := (isPathConnected_compl_closedBall hd (0 : E) r).isConnected
  obtain ⟨x, hx⟩ := hconn.nonempty
  have hout : (_root_.Metric.closedBall (0 : E) r)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hKr
  have hcomponent : (_root_.Metric.closedBall (0 : E) r)ᶜ ⊆ connectedComponentIn Kᶜ x :=
    hconn.isPreconnected.subset_connectedComponentIn hx hout
  refine ⟨x, hout hx, ?_⟩
  intro hbounded
  have hbound : Bornology.IsBounded (_root_.Metric.closedBall (0 : E) r ∪ (_root_.Metric.closedBall (0 : E) r)ᶜ) :=
    isBounded_closedBall.union (hbounded.subset hcomponent)
  rw [_root_.Set.union_compl_self] at hbound
  exact NormedSpace.unbounded_univ ℝ E hbound

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.Topology.IsCompact
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.IsCompact.exists_not_isBounded_connectedComponentIn_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.IsCompact.exists_not_isBounded_connectedComponentIn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.IsCompact.exists_not_isBounded_connectedComponentIn_compl ``Submission.DifferentialGeometry.Topology.IsCompact.exists_not_isBounded_connectedComponentIn_compl

end DifferentialGeometry.Topology
