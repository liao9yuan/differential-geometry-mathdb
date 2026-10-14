import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.Filter _root_.Metric
open scoped _root_.Topology

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_infDist_gt_of_not_isCompact_closure {K U : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hU : ¬ IsCompact (closure U)) (R : ℝ) :
    ∃ x ∈ U, R < _root_.Metric.infDist x K := by
  classical
  by_contra hnone
  have hsub : U ⊆ _root_.Metric.cthickening R K := by
    intro x hx
    have hbound : _root_.Metric.infDist x K ≤ R := le_of_not_gt (fun h => hnone ⟨x, hx, h⟩)
    obtain ⟨y, hy, hdist⟩ := hK.exists_infDist_eq_dist hKne x
    exact _root_.Metric.mem_cthickening_of_dist_le x y R K hy (hdist ▸ hbound)
  exact hU (hK.cthickening.of_isClosed_subset isClosed_closure
    (closure_minimal hsub _root_.Metric.isClosed_cthickening))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_infDist_gt_of_not_isCompact_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_infDist_gt_of_not_isCompact_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_infDist_gt_of_not_isCompact_closure ``Submission.DifferentialGeometry.Geometry.Topology.exists_infDist_gt_of_not_isCompact_closure

theorem exists_tendsto_infDist_atTop_of_not_isCompact_closure {K U : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty) (hU : ¬ IsCompact (closure U)) :
    ∃ x : ℕ → X, (∀ n, x n ∈ U) ∧ (∀ n : ℕ, (n : ℝ) < _root_.Metric.infDist (x n) K) ∧
      Tendsto (fun n => _root_.Metric.infDist (x n) K) _root_.Filter.atTop atTop := by
  classical
  choose x hx hdist using fun n : ℕ =>
    exists_infDist_gt_of_not_isCompact_closure hK hKne hU (n : ℝ)
  refine ⟨x, hx, hdist, tendsto_atTop.2 fun R => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  exact (hN.trans_le hcast).le.trans (hdist n).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_tendsto_infDist_atTop_of_not_isCompact_closure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_tendsto_infDist_atTop_of_not_isCompact_closure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_tendsto_infDist_atTop_of_not_isCompact_closure ``Submission.DifferentialGeometry.Geometry.Topology.exists_tendsto_infDist_atTop_of_not_isCompact_closure

end DifferentialGeometry.Geometry.Topology
