/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.HalfSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))
local notation "E'" => EuclideanSpace ℝ (Fin ((d + 1) + 1))

theorem embeddingOrientationParity_eq_of_preserves_halfspaces
    {f : E → E} {F : E' → E'} {V : Set E} {U : Set E'}
    (hV : IsOpen V) (hU : IsOpen U) (hf : ContinuousOn f V) (hfi : _root_.Set.InjOn f V)
    (hF : ContinuousOn F U) (hFi : _root_.Set.InjOn F U)
    (hV0 : (0 : E) ∈ V) (hU0 : (0 : E') ∈ U) (hf0 : f 0 = 0) (hF0 : F 0 = 0)
    (htrace : ∀ y ∈ U, (euclideanProductChart d y).2 = 0 →
      F y = euclideanProductPoint d (f (euclideanProductChart d y).1) 0)
    (hpos : ∀ y ∈ U, 0 < (euclideanProductChart d y).2 →
      0 < (euclideanProductChart d (F y)).2)
    (hneg : ∀ y ∈ U, (euclideanProductChart d y).2 < 0 →
      (euclideanProductChart d (F y)).2 < 0) :
    embeddingOrientationParity hU hF hFi ⟨0, hU0⟩ =
      embeddingOrientationParity hV hf hfi ⟨0, hV0⟩ := by
  obtain ⟨a, ha, haU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hU0)
  obtain ⟨b, hb, hbV⟩ := nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hV0)
  let R := _root_.Min.min a b
  have hR : 0 < R := lt_min ha hb
  have hRU : _root_.Metric.closedBall (0 : E') R ⊆ U :=
    (_root_.Metric.closedBall_subset_closedBall (min_le_left a b)).trans haU
  have hRV : _root_.Metric.closedBall (0 : E) R ⊆ V :=
    (_root_.Metric.closedBall_subset_closedBall (min_le_right a b)).trans hbV
  have hfR : IsolatingRadius f 0 R := by
    simpa only [hf0, sub_zero] using isolatingRadius_sub_of_injOn hf hfi hR hRV
  have hFR : IsolatingRadius F 0 R := by
    simpa only [hF0, sub_zero] using isolatingRadius_sub_of_injOn hF hFi hR hRU
  have hfiR := hfi.mono (ball_subset_closedBall.trans hRV)
  have hFiR := hFi.mono (ball_subset_closedBall.trans hRU)
  have h₁ := embeddingOrientationParity_congr hU _root_.Metric.isOpen_ball hF hFi
    (hFR.continuousOn.mono _root_.Metric.ball_subset_closedBall) hFiR hU0 (_root_.Metric.mem_ball_self hR)
    Filter.EventuallyEq.rfl
  have h₂ := embeddingOrientationParity_congr _root_.Metric.isOpen_ball hV
    (hfR.continuousOn.mono _root_.Metric.ball_subset_closedBall) hfiR hf hfi (_root_.Metric.mem_ball_self hR) hV0
    Filter.EventuallyEq.rfl
  have hmiddle := embeddingOrientationParity_eq_of_preserves_normal_sides hfR hFR hfiR hFiR
    (fun y hy => htrace y (hRU (_root_.Metric.sphere_subset_closedBall hy)))
    (fun y hy => hpos y (hRU (_root_.Metric.sphere_subset_closedBall hy)))
    (fun y hy => hneg y (hRU (_root_.Metric.sphere_subset_closedBall hy)))
  exact h₁.trans (hmiddle.trans h₂)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_halfspaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_halfspaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_halfspaces ``Submission.DifferentialGeometry.LocalDegree.embeddingOrientationParity_eq_of_preserves_halfspaces

end DifferentialGeometry.LocalDegree
