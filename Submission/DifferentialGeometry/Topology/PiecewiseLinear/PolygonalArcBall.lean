/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Submission.DifferentialGeometry.External.Schoenflies.PolyArcRealize

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.Schoenflies

theorem isPLBall_one_polyArc_carrier {n : ℕ} (A : PolyArc n) : IsPLBall 1 A.carrier := by
  have hprefix : ∀ k ≤ n, IsPLBall 1 (A.prefixCarrier k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [A.prefixCarrier_zero]
      exact isPLBall_segment A.vertex_ne
    | succ k ih =>
      intro hk
      rw [A.prefixCarrier_succ]
      exact isPLBall_union_of_isArcBetween (ih (by omega)) (isPLBall_segment A.vertex_ne)
        (A.isArcBetween_prefixCarrier k (by omega))
        (isArcBetween_segment A.vertex_ne) (A.prefixCarrier_meet hk)
  exact hprefix n le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_polyArc_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_polyArc_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_polyArc_carrier ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_polyArc_carrier

theorem isPLBall_one_of_isArcBetween_of_isPolygonal {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hpoly : IsPolygonal A) : IsPLBall 1 A := by
  obtain ⟨n, P, hP, _, _⟩ := isPolyArcCarrier_of_isPolygonal hA hpoly
  exact hP ▸ isPLBall_one_polyArc_carrier P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_of_isArcBetween_of_isPolygonal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_of_isArcBetween_of_isPolygonal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_of_isArcBetween_of_isPolygonal ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_one_of_isArcBetween_of_isPolygonal

end DifferentialGeometry.Topology.PiecewiseLinear
