import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Positivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set
open scoped _root_.NNReal

namespace DifferentialGeometry.Analysis

private theorem exists_frontier_mem_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {x y : E} (hx : x ∈ U) (hy : y ∉ U) :
    ∃ q, q ∈ segment ℝ x y ∧ q ∈ frontier U := by
  by_contra h
  have hfront : ∀ q ∈ segment ℝ x y, q ∉ frontier U := by
    simpa only [not_exists, not_and] using h
  have hclosure : closure U ∩ segment ℝ x y ⊆ U := by
    intro q hq
    by_contra hqU
    exact hfront q hq.2 (by simpa only [frontier, hU.interior_eq, _root_.Set.mem_sdiff] using ⟨hq.1, hqU⟩)
  have hsub := (convex_segment x y).isPreconnected.subset_of_closure_inter_subset hU
    ⟨x, left_mem_segment ℝ x y, hx⟩ hclosure
  exact hy (hsub (right_mem_segment ℝ x y))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.exists_frontier_mem_segment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.exists_frontier_mem_segment target :: scope.openDecls } }

open _root_.Classical in
open _root_.LipschitzOnWith in
theorem _root_.Submission.LipschitzOnWith.piecewise_const_of_eq_on_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]
    {U K : Set E} {f : E → F} {c : F} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (closure U ∩ K)) (hU : IsOpen U) (hK : Convex ℝ K)
    (hfront : ∀ q ∈ frontier U ∩ K, f q = c) :
    LipschitzOnWith L (U.piecewise f (fun _ => c)) K := by
  classical
  have hcross {x y : E} (hx : x ∈ K) (hy : y ∈ K) (hxU : x ∈ U) (hyU : y ∉ U) :
      dist (f x) c ≤ L * _root_.Dist.dist x y := by
    obtain ⟨q, hqseg, hqfront⟩ := exists_frontier_mem_segment hU hxU hyU
    have hqK : q ∈ K := hK.segment_subset hx hy hqseg
    have hdist : _root_.Dist.dist x q ≤ _root_.Dist.dist x y := by
      have hh := segment_subset_closedBall_left x y hqseg
      simpa only [Metric.mem_closedBall, dist_comm q x] using hh
    rw [← hfront q ⟨hqfront, hqK⟩]
    exact (hf.dist_le_mul x ⟨subset_closure hxU, hx⟩ q
      ⟨frontier_subset_closure hqfront, hqK⟩).trans
      (mul_le_mul_of_nonneg_left hdist L.coe_nonneg)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  by_cases hxU : x ∈ U
  · by_cases hyU : y ∈ U
    · rw [_root_.Set.piecewise_eq_of_mem U f (fun _ => c) hxU,
        _root_.Set.piecewise_eq_of_mem U f (fun _ => c) hyU]
      exact hf.dist_le_mul x ⟨subset_closure hxU, hx⟩ y ⟨subset_closure hyU, hy⟩
    · rw [_root_.Set.piecewise_eq_of_mem U f (fun _ => c) hxU,
        _root_.Set.piecewise_eq_of_notMem U f (fun _ => c) hyU]
      exact hcross hx hy hxU hyU
  · by_cases hyU : y ∈ U
    · rw [_root_.Set.piecewise_eq_of_notMem U f (fun _ => c) hxU,
        _root_.Set.piecewise_eq_of_mem U f (fun _ => c) hyU, dist_comm]
      simpa only [dist_comm y x] using hcross hy hx hyU hxU
    · rw [_root_.Set.piecewise_eq_of_notMem U f (fun _ => c) hxU,
        _root_.Set.piecewise_eq_of_notMem U f (fun _ => c) hyU, dist_self]
      positivity

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.LipschitzOnWith
  let env ← Lean.getEnv
  if env.contains `LipschitzOnWith.piecewise_const_of_eq_on_frontier then
    throwError "Refusing to shadow existing declaration LipschitzOnWith.piecewise_const_of_eq_on_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzOnWith.piecewise_const_of_eq_on_frontier ``Submission.LipschitzOnWith.piecewise_const_of_eq_on_frontier

open _root_.Classical in
open _root_.LipschitzOnWith in
theorem _root_.Submission.LipschitzOnWith.piecewise_sub_const_of_eq_on_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {U K : Set E} {f : E → F} {c : F} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (closure U ∩ K)) (hU : IsOpen U) (hK : Convex ℝ K)
    (hfront : ∀ q ∈ frontier U ∩ K, f q = c) :
    LipschitzOnWith L (U.piecewise (fun x => f x - c) (fun _ => 0)) K := by
  classical
  have hsub : LipschitzOnWith L (fun x => f x - c) (closure U ∩ K) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_sub_right] using hf.dist_le_mul x hx y hy
  exact hsub.piecewise_const_of_eq_on_frontier hU hK (fun q hq => by rw [hfront q hq, sub_self])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzOnWith.piecewise_sub_const_of_eq_on_frontier then
    throwError "Refusing to shadow existing declaration LipschitzOnWith.piecewise_sub_const_of_eq_on_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzOnWith.piecewise_sub_const_of_eq_on_frontier ``Submission.LipschitzOnWith.piecewise_sub_const_of_eq_on_frontier

open _root_.Classical in
open _root_.LipschitzOnWith in
theorem _root_.Submission.LipschitzOnWith.piecewise_sub_const_on_ball_of_eq_on_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    {U : Set E} {f : E → F} {c : F} {L : ℝ≥0} {p : E} {R : ℝ}
    (hf : LipschitzOnWith L f (closure U ∩ Metric.ball p R)) (hU : IsOpen U)
    (hfront : ∀ q ∈ frontier U ∩ Metric.ball p R, f q = c) :
    LipschitzOnWith L (U.piecewise (fun x => f x - c) (fun _ => 0)) (Metric.ball p R) :=
  hf.piecewise_sub_const_of_eq_on_frontier hU (convex_ball p R) hfront

run_cmd do
  let env ← Lean.getEnv
  if env.contains `LipschitzOnWith.piecewise_sub_const_on_ball_of_eq_on_frontier then
    throwError "Refusing to shadow existing declaration LipschitzOnWith.piecewise_sub_const_on_ball_of_eq_on_frontier"
  Lean.modifyEnv fun env => Lean.addAlias env `LipschitzOnWith.piecewise_sub_const_on_ball_of_eq_on_frontier ``Submission.LipschitzOnWith.piecewise_sub_const_on_ball_of_eq_on_frontier

end DifferentialGeometry.Analysis

end

end
