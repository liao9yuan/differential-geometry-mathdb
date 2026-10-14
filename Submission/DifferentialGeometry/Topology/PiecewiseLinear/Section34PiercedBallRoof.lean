/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedBallHeightMove
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem square_closedBall_eq (r : ℝ) :
    Metric.closedBall (0 : ℝ × ℝ) r = _root_.Set.Icc (-r) r ×ˢ _root_.Set.Icc (-r) r := by
  ext x
  simp only [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, max_le_iff,
    abs_le, _root_.Set.mem_prod, _root_.Set.mem_Icc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_closedBall_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_closedBall_eq target :: scope.openDecls } }

private theorem square_closedBall_isHPolytope (r : ℝ) :
    IsHPolytope (Metric.closedBall (0 : ℝ × ℝ) r) := by
  rw [square_closedBall_eq]
  exact isHPolytope_Icc.prod isHPolytope_Icc

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.square_closedBall_isHPolytope
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.PiecewiseLinear.square_closedBall_isHPolytope target :: scope.openDecls } }

theorem isPLBall_square_closedBall {r : ℝ} (hr : 0 < r) :
    IsPLBall 2 (Metric.closedBall (0 : ℝ × ℝ) r) := by
  have hinter : (interior (Metric.closedBall (0 : ℝ × ℝ) r)).Nonempty := by
    rw [interior_closedBall _ hr.ne']
    exact ⟨0, Metric.mem_ball_self hr⟩
  simpa only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd] using
    (square_closedBall_isHPolytope r).isPLBall hinter

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_square_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_square_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_square_closedBall ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_square_closedBall

theorem exists_piercing_square_roof_with_sign_closures {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKP : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1)) {a : ℝ} (ha : 0 < a) :
    ∃ g : (ℝ × ℝ) → ℝ, IsPiecewiseAffineOn g _root_.Set.univ ∧
      (∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1, |g x| ≤ a / 2) ∧
      (∀ x ∈ frontier (Metric.closedBall (0 : ℝ × ℝ) 1), g x < 0) ∧
      (∀ x ∈ K, 0 < g x) ∧
      IsPLSphere 1 {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} ∧
      ({x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} ⊆
        closure (interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∩ {x | 0 < g x})) ∧
      {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} ⊆
        closure (interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∩ {x | g x < 0}) := by
  have hKnorm (x) (hx : x ∈ K) : ‖x‖ < 1 := by
    have hm := hKP hx
    rwa [interior_closedBall _ one_ne_zero, mem_ball_zero_iff] at hm
  obtain ⟨r, hr, hr1, hKr⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ K, ‖x‖ < r := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      simp only [hKe, _root_.Set.mem_empty_iff_false, false_implies, implies_true]
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
      refine ⟨(‖x‖ + 1) / 2, by positivity, by linarith [hKnorm x hx], ?_⟩
      intro y hy
      exact (hmax hy).trans_lt (by linarith [hKnorm x hx])
  let c := a / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let g : (ℝ × ℝ) → ℝ := fun x => c * (r - ‖x‖)
  have hnorm : IsPiecewiseAffineOn (_root_.Norm.norm : (ℝ × ℝ) → ℝ) univ := by
    have hfst : IsPiecewiseAffineOn (Prod.fst : ℝ × ℝ → ℝ) univ :=
      isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ ℝ ℝ).toAffineMap isOpen_univ
    have hsnd : IsPiecewiseAffineOn (Prod.snd : ℝ × ℝ → ℝ) univ :=
      isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ ℝ ℝ).toAffineMap isOpen_univ
    convert hfst.abs.max hsnd.abs using 1
    ext x
    exact (Prod.norm_def x).trans (by rw [Real.norm_eq_abs, Real.norm_eq_abs])
  have hg : IsPiecewiseAffineOn g univ := by
    let A : ℝ →ᵃ[ℝ] ℝ := (-c) • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (c * r)
    have hcomp := (isPiecewiseAffineOn_of_affine A isOpen_univ).comp hnorm
    simp only [_root_.Set.preimage_univ, _root_.Set.inter_univ] at hcomp
    convert hcomp using 1
    ext x
    change c * (r - ‖x‖) = -c * ‖x‖ + c * r
    ring
  have hzero : {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} =
      Metric.sphere (0 : ℝ × ℝ) r := by
    ext x
    simp only [_root_.Set.mem_ofPred_eq, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨-, hx⟩
      have hx' : r - ‖x‖ = 0 := (mul_eq_zero.mp hx).resolve_left hc.ne'
      linarith
    · intro hx
      exact ⟨hx ▸ hr1.le, by dsimp [g]; rw [hx, sub_self, _root_.MulZeroClass.mul_zero]⟩
  refine ⟨g, hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hn := mem_closedBall_zero_iff.mp hx
    have hnonneg := norm_nonneg x
    dsimp [g, c]
    apply abs_le.mpr
    constructor <;> nlinarith
  · intro x hx
    rw [frontier_closedBall _ one_ne_zero, mem_sphere_zero_iff_norm] at hx
    dsimp [g]
    rw [hx]
    exact mul_neg_of_pos_of_neg hc (sub_neg.mpr hr1)
  · intro x hx
    exact mul_pos hc (sub_pos.mpr (hKr x hx))
  · rw [hzero, ← frontier_closedBall _ hr.ne']
    exact (square_closedBall_isHPolytope r).isPLSphere_frontier
      (by simp only [Module.finrank_prod, Module.finrank_self, Nat.reduceAdd])
      (by rw [interior_closedBall _ hr.ne']; exact ⟨0, Metric.mem_ball_self hr⟩)
  · rw [hzero]
    have he : interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∩ {x | 0 < g x} =
        Metric.ball (0 : ℝ × ℝ) r := by
      ext x
      rw [interior_closedBall _ one_ne_zero]
      simp only [_root_.Set.mem_inter_iff, mem_ball_zero_iff, _root_.Set.mem_ofPred_eq]
      change (‖x‖ < 1 ∧ 0 < c * (r - ‖x‖)) ↔ ‖x‖ < r
      rw [mul_pos_iff_of_pos_left hc, sub_pos]
      exact ⟨And.right, fun hx => ⟨hx.trans hr1, hx⟩⟩
    rw [he, closure_ball _ hr.ne']
    exact Metric.sphere_subset_closedBall
  · rw [hzero]
    have he : interior (Metric.closedBall (0 : ℝ × ℝ) 1) ∩ {x | g x < 0} =
        Metric.ball (0 : ℝ × ℝ) 1 ∩ (Metric.closedBall (0 : ℝ × ℝ) r)ᶜ := by
      ext x
      rw [interior_closedBall _ one_ne_zero]
      simp only [_root_.Set.mem_inter_iff, mem_ball_zero_iff, _root_.Set.mem_compl_iff, mem_closedBall_zero_iff,
        _root_.Set.mem_ofPred_eq, not_le]
      change (‖x‖ < 1 ∧ c * (r - ‖x‖) < 0) ↔ (‖x‖ < 1 ∧ r < ‖x‖)
      constructor
      · rintro ⟨hx, hgx⟩
        exact ⟨hx, by nlinarith⟩
      · rintro ⟨hx, hgx⟩
        exact ⟨hx, mul_neg_of_pos_of_neg hc (sub_neg.mpr hgx)⟩
    rw [he]
    intro x hx
    have hxnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
    apply Metric.isOpen_ball.inter_closure
    refine ⟨mem_ball_zero_iff.mpr (hxnorm ▸ hr1), ?_⟩
    have hxfront : x ∈ frontier (Metric.closedBall (0 : ℝ × ℝ) r) := by
      rwa [frontier_closedBall _ hr.ne']
    rw [frontier_eq_closure_inter_closure] at hxfront
    exact hxfront.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof_with_sign_closures then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof_with_sign_closures"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof_with_sign_closures ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof_with_sign_closures

theorem exists_piercing_square_roof {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKP : K ⊆ interior (Metric.closedBall (0 : ℝ × ℝ) 1)) {a : ℝ} (ha : 0 < a) :
    ∃ g : (ℝ × ℝ) → ℝ, IsPiecewiseAffineOn g _root_.Set.univ ∧
      (∀ x ∈ Metric.closedBall (0 : ℝ × ℝ) 1, |g x| ≤ a / 2) ∧
      (∀ x ∈ frontier (Metric.closedBall (0 : ℝ × ℝ) 1), g x < 0) ∧
      (∀ x ∈ K, 0 < g x) ∧
      IsPLSphere 1 {x | x ∈ Metric.closedBall (0 : ℝ × ℝ) 1 ∧ g x = 0} := by
  obtain ⟨g, hg, hga, hgf, hgK, hzero, -⟩ :=
    exists_piercing_square_roof_with_sign_closures hK hKP ha
  exact ⟨g, hg, hga, hgf, hgK, hzero⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_piercing_square_roof

end DifferentialGeometry.Topology.PiecewiseLinear
