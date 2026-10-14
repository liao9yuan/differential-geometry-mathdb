import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.Support

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem nirenbergTestFunction_apply
    (k : Fin d) (h : ℝ) (η u : E → ℝ) (x : E) (hh : h ≠ 0) :
    nirenbergTestFunction k h η u x =
      ((η (x + (-h) • EuclideanSpace.single k 1))^2 *
          diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) -
        (η x)^2 * diffQuot k h u x) / (-h) := by
  change diffQuot k (-h) (fun y : E => η y ^ 2 * diffQuot k h u y) x = _
  rw [diffQuot_apply_of_ne (d := d) k (neg_ne_zero.mpr hh)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_apply

omit [NeZero d] in
@[simp] lemma nirenbergTestFunction_zero_h
    (k : Fin d) (η u : E → ℝ) :
    nirenbergTestFunction k 0 η u = 0 := by
  funext x
  change diffQuot k (-(0 : ℝ)) (fun y : E => η y ^ 2 * diffQuot k 0 u y) x = 0
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_zero_h then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_zero_h"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_zero_h ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_zero_h

omit [NeZero d] in
theorem nirenbergTestFunction_support_subset
    (k : Fin d) (h : ℝ) {η : E → ℝ}
    (u : E → ℝ) :
    Function.support (nirenbergTestFunction k h η u) ⊆
      tsupport η ∪
        {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases hh : h = 0
  · exfalso
    apply hx
    subst hh
    change diffQuot k (-(0 : ℝ)) (fun y : E => η y ^ 2 * diffQuot k 0 u y) x = 0
    simp
  · have h_apply := nirenbergTestFunction_apply (d := d) k h η u x hh
    rw [h_apply] at hx
    have h_num_ne : (η (x + (-h) • EuclideanSpace.single k 1))^2 *
        diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) -
        (η x)^2 * diffQuot k h u x ≠ 0 := by
      intro h_zero
      apply hx
      rw [h_zero, zero_div]
    by_cases hηx : η x = 0
    · right
      have hFx_zero : (η x)^2 * diffQuot k h u x = 0 := by
        rw [show (η x)^2 = 0 from by rw [hηx]; ring, _root_.MulZeroClass.zero_mul]
      rw [hFx_zero, sub_zero] at h_num_ne
      have hηy_ne : η (x + (-h) • EuclideanSpace.single k 1) ≠ 0 := by
        intro h_zero
        apply h_num_ne
        rw [show (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 from by
          rw [h_zero]; ring, _root_.MulZeroClass.zero_mul]
      exact subset_tsupport η hηy_ne
    · left
      exact subset_tsupport η hηx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_support_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_support_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_support_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_support_subset

omit [NeZero d] in
theorem nirenbergTestFunction_tsupport_subset
    (k : Fin d) (h : ℝ) {η : E → ℝ}
    (u : E → ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆
      tsupport η ∪
        {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} := by
  have htrans_cont : Continuous
      (fun x : E => x + (-h) • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_pre_closed : IsClosed
      {x : E | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} :=
    (isClosed_tsupport η).preimage htrans_cont
  have h_rhs_closed : IsClosed
      (tsupport η ∪
        {x : E | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η}) :=
    (isClosed_tsupport η).union h_pre_closed
  refine closure_minimal ?_ h_rhs_closed
  exact nirenbergTestFunction_support_subset (d := d) k h u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_tsupport_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_tsupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_tsupport_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction_tsupport_subset


omit [NeZero d] in
theorem hasCompactSupport_nirenbergTestFunction
    {η u : E → ℝ} (hη_support : HasCompactSupport η)
    (k : Fin d) (h : ℝ) :
    HasCompactSupport (nirenbergTestFunction k h η u) := by
  unfold nirenbergTestFunction
  have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
    have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
      funext y
      ring
    rw [heq]
    exact hη_support.mul_right
  have h_prod_support :
      HasCompactSupport
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) :=
    h_eta_sq_support.mul_right
  exact hasCompactSupport_diffQuot_of_hasCompactSupport
    (d := d) h_prod_support k (-h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasCompactSupport_nirenbergTestFunction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasCompactSupport_nirenbergTestFunction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasCompactSupport_nirenbergTestFunction ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasCompactSupport_nirenbergTestFunction

omit [NeZero d] in
private lemma support_eta_sq_subset
    (η : E → ℝ) :
    Function.support (fun y : E => η y ^ 2) ⊆ Function.support η := by
  intro y hy
  by_contra hyη
  rw [Function.notMem_support] at hyη
  apply hy
  change η y ^ 2 = 0
  rw [hyη]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.support_eta_sq_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.support_eta_sq_subset target :: scope.openDecls } }

omit [NeZero d] in
private lemma support_eta_sq_diffQuot_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    Function.support
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) ⊆
      Function.support η := by
  intro y hy
  have hsq_ne : η y ^ 2 ≠ 0 := by
    intro hsq
    apply hy
    change η y ^ 2 *
        DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y = 0
    rw [hsq, _root_.MulZeroClass.zero_mul]
  intro hyη
  apply hsq_ne
  rw [hyη]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.support_eta_sq_diffQuot_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.support_eta_sq_diffQuot_subset target :: scope.openDecls } }

omit [NeZero d] in
private lemma tsupport_eta_sq_diffQuot_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    tsupport
        (fun y : E => η y ^ 2 *
          DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y) ⊆
      tsupport η := by
  exact closure_mono (support_eta_sq_diffQuot_subset (d := d) η u k h)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_eta_sq_diffQuot_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_eta_sq_diffQuot_subset target :: scope.openDecls } }

omit [NeZero d] in
theorem tsupport_nirenbergTestFunction_subset
    (η u : E → ℝ) (k : Fin d) (h : ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆
      Metric.cthickening |h| (tsupport η) := by
  unfold nirenbergTestFunction
  set g : E → ℝ := fun y : E => η y ^ 2 *
    DifferentialGeometry.Analysis.Sobolev.diffQuot k h u y with hg_def
  have h_thick_closed : IsClosed (Metric.cthickening |h| (tsupport η)) :=
    _root_.Metric.isClosed_cthickening
  have h_self_subset_thick : tsupport η ⊆ Metric.cthickening |h| (tsupport η) :=
    _root_.Metric.self_subset_cthickening _
  have h_shift_in_thick :
      ∀ y₀ ∈ tsupport η,
        y₀ - (-h) • EuclideanSpace.single k 1 ∈
          Metric.cthickening |h| (tsupport η) := by
    intro y₀ hy₀
    refine Metric.mem_cthickening_of_dist_le _ y₀ |h| (tsupport η) hy₀ ?_
    have hsing_norm :
        ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
    have hdist_eq :
        _root_.Dist.dist (y₀ - (-h) • EuclideanSpace.single k 1) y₀ =
          ‖(-h) • EuclideanSpace.single k (1 : ℝ)‖ := by
      rw [dist_eq_norm]
      have :
          (y₀ - (-h) • EuclideanSpace.single k 1) - y₀ =
            -((-h) • EuclideanSpace.single k 1) := by
        rw [sub_right_comm, sub_self, zero_sub]
      rw [this, norm_neg]
    rw [hdist_eq]
    rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs, abs_neg]
  have h_support_subset :
      Function.support
          (DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) g) ⊆
        Metric.cthickening |h| (tsupport η) := by
    intro x hx
    have hx_ne : DifferentialGeometry.Analysis.Sobolev.diffQuot k (-h) g x ≠ 0 :=
      hx
    by_cases hh : h = 0
    · subst hh
      exfalso
      apply hx_ne
      have hzeroNeg : (-(0 : ℝ)) = 0 := neg_zero
      rw [hzeroNeg]
      change DifferentialGeometry.Analysis.Sobolev.diffQuot k 0 g x = 0
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_zero_h]
      rfl
    · have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
      rw [DifferentialGeometry.Analysis.Sobolev.diffQuot_apply_of_ne
        (d := d) k hnh g x] at hx_ne
      have hnum_ne : g (x + (-h) • EuclideanSpace.single k 1) - g x ≠ 0 := by
        intro hnum
        apply hx_ne
        rw [hnum, zero_div]
      have h_or :
          g (x + (-h) • EuclideanSpace.single k 1) ≠ 0 ∨ g x ≠ 0 := by
        by_contra hboth
        rw [not_or] at hboth
        obtain ⟨hb1, hb2⟩ := hboth
        have hb1' : g (x + (-h) • EuclideanSpace.single k 1) = 0 :=
          not_not.mp hb1
        have hb2' : g x = 0 := not_not.mp hb2
        apply hnum_ne
        rw [hb1', hb2', sub_zero]
      cases h_or with
      | inl h1 =>
        have h_in_support_g :
            x + (-h) • EuclideanSpace.single k 1 ∈ Function.support g :=
          h1
        have h_in_support_η :
            x + (-h) • EuclideanSpace.single k 1 ∈ Function.support η :=
          support_eta_sq_diffQuot_subset (d := d) η u k h h_in_support_g
        have h_in_tsupp_η :
            x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η :=
          subset_closure h_in_support_η
        have h_x_eq :
            x =
              (x + (-h) • EuclideanSpace.single k 1) -
                (-h) • EuclideanSpace.single k 1 := by
          rw [add_sub_cancel_right]
        rw [h_x_eq]
        exact h_shift_in_thick _ h_in_tsupp_η
      | inr h2 =>
        have h_in_support_g : x ∈ Function.support g := h2
        have h_in_support_η : x ∈ Function.support η :=
          support_eta_sq_diffQuot_subset (d := d) η u k h h_in_support_g
        have h_in_tsupp_η : x ∈ tsupport η := subset_closure h_in_support_η
        exact h_self_subset_thick h_in_tsupp_η
  exact (closure_minimal h_support_subset h_thick_closed)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.tsupport_nirenbergTestFunction_subset


end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
