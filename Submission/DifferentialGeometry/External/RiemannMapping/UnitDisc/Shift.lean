/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

module
public import Mathlib.Analysis.Complex.UnitDisc.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-!
# Shift on the unit disc

In this file we define `Complex.UnitDisc.shift z` to be the automorphism of the unit disc
that sends `0` to `z` and preserves the diameter joining `0` to `z`.

We also prove basic properties of this function.
-/

open _root_.Set _root_.Function _root_.Metric
open scoped _root_.ComplexConjugate

noncomputable section

namespace Complex.UnitDisc
open _root_.Complex _root_.Complex.UnitDisc

public section

open _root_.Complex _root_.Complex.UnitDisc in
lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (_root_.Star.star z * w).one_add_coe_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_den_ne_zero then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_den_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_den_ne_zero ``Submission.Complex.UnitDisc.shift_den_ne_zero

open _root_.Complex _root_.Complex.UnitDisc in
lemma shift_den_ne_zero' (z w : 𝔻) : 1 + z * conj (w : ℂ) ≠ 0 :=
  (z * _root_.Star.star w).one_add_coe_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_den_ne_zero' then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_den_ne_zero'"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_den_ne_zero' ``Submission.Complex.UnitDisc.shift_den_ne_zero'

end

open _root_.Complex _root_.Complex.UnitDisc in
theorem norm_shiftFun_le (z w : 𝔻) :
    ‖(z + w : ℂ) / (1 + conj ↑z * w)‖ ≤ (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) := by
  have hz := z.sq_norm_lt_one
  have hw := w.sq_norm_lt_one
  have hzw : z.re * w.re + z.im * w.im ≤ ‖(z : ℂ)‖ * ‖(w : ℂ)‖ := by
    rw [_root_.Complex.norm_def, _root_.Complex.norm_def, ← Real.sqrt_mul, _root_.Complex.normSq_apply, _root_.Complex.normSq_apply]
    · apply Real.le_sqrt_of_sq_le
      linear_combination (norm := {apply le_of_eq; simp; ring})
        sq_nonneg (z.re * w.im - z.im * w.re)
    · apply _root_.Complex.normSq_nonneg
  rw [norm_div, div_le_div_iff₀, ← sq_le_sq₀]
  · rw [← sub_nonneg] at hzw
    simp [mul_pow, RCLike.norm_sq_eq_def, add_sq] at hz hw ⊢
    linear_combination 2 * mul_nonneg hzw (mul_nonneg (sub_nonneg.2 hz.le) (sub_nonneg.2 hw.le))
  any_goals positivity
  simpa using shift_den_ne_zero z w

run_cmd do
  let target := ``Submission.Complex.UnitDisc.norm_shiftFun_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.UnitDisc.norm_shiftFun_le target :: scope.openDecls } }

open _root_.Complex _root_.Complex.UnitDisc in
/-- Auxiliary definition for `shift` below. This function is not a part of the public API. -/
def shiftFun (z w : 𝔻) : 𝔻 :=
  _root_.Complex.UnitDisc.mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    refine (norm_shiftFun_le _ _).trans_lt ?_
    rw [div_lt_one (by positivity)]
    nlinarith only [z.norm_lt_one, w.norm_lt_one]

run_cmd do
  let target := ``Submission.Complex.UnitDisc.shiftFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.UnitDisc.shiftFun target :: scope.openDecls } }

open _root_.Complex _root_.Complex.UnitDisc in
theorem coe_shiftFun (z w : 𝔻) : (shiftFun z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

run_cmd do
  let target := ``Submission.Complex.UnitDisc.coe_shiftFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.UnitDisc.coe_shiftFun target :: scope.openDecls } }

open _root_.Complex _root_.Complex.UnitDisc in
theorem shiftFun_eq_iff {z w u : 𝔻} : shiftFun z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w := by
  rw [← _root_.Complex.UnitDisc.coe_inj, coe_shiftFun, div_eq_iff (shift_den_ne_zero _ _)]
  ring_nf

run_cmd do
  let target := ``Submission.Complex.UnitDisc.shiftFun_eq_iff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.UnitDisc.shiftFun_eq_iff target :: scope.openDecls } }

open _root_.Complex _root_.Complex.UnitDisc in
theorem shiftFun_neg_apply_shiftFun (z w : 𝔻) : shiftFun (-z) (shiftFun z w) = w := by
  rw [shiftFun_eq_iff, coe_shiftFun, add_div_eq_mul_add_div, ← mul_div_assoc,
    add_div_eq_mul_add_div]
  · simp; ring
  all_goals exact shift_den_ne_zero z w

run_cmd do
  let target := ``Submission.Complex.UnitDisc.shiftFun_neg_apply_shiftFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.UnitDisc.shiftFun_neg_apply_shiftFun target :: scope.openDecls } }

public section

open _root_.Complex _root_.Complex.UnitDisc in
/-- The automorphism of the unit disc that sends zero to `z`. -/
def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun _
  right_inv w := by simpa using shiftFun_neg_apply_shiftFun (-z) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift ``Submission.Complex.UnitDisc.shift

open _root_.Complex _root_.Complex.UnitDisc in
/-- An explicit formula for `shift z w`.

Note that the definition of `shift` is not exposed, so this is not a `dsimp` lemma. -/
theorem coe_shift (z w : 𝔻) : (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := by rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.coe_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.coe_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.coe_shift ``Submission.Complex.UnitDisc.coe_shift

open _root_.Complex _root_.Complex.UnitDisc in
theorem shift_eq_iff {z w u : 𝔻} : shift z w = u ↔ (z + w : ℂ) = u + u * conj ↑z * w :=
  shiftFun_eq_iff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_eq_iff then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_eq_iff ``Submission.Complex.UnitDisc.shift_eq_iff

open _root_.Complex _root_.Complex.UnitDisc in
theorem symm_shift (z : 𝔻) : (shift z).symm = shift (-z) := by
  ext1
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.symm_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.symm_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.symm_shift ``Submission.Complex.UnitDisc.symm_shift

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem star_shift (z w : 𝔻) : _root_.Star.star (shift z w) = shift (_root_.Star.star z) (_root_.Star.star w) :=
  _root_.Complex.UnitDisc.coe_injective <| by simp [coe_shift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.star_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.star_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.star_shift ``Submission.Complex.UnitDisc.star_shift

open _root_.Complex _root_.Complex.UnitDisc in
theorem norm_shift_swap (z w : 𝔻) : ‖(shift z w : ℂ)‖ = ‖(shift w z : ℂ)‖ := by
  rw [coe_shift, norm_div, ← _root_.Complex.norm_conj (1 + _)]
  simp [coe_shift, add_comm, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.norm_shift_swap then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.norm_shift_swap"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.norm_shift_swap ``Submission.Complex.UnitDisc.norm_shift_swap

open _root_.Complex _root_.Complex.UnitDisc in
theorem neg_shift (z w : 𝔻) : -shift z w = shift (-z) (-w) := by
  ext1
  simp [coe_shift, ← neg_add_rev, add_comm, neg_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.neg_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.neg_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.neg_shift ``Submission.Complex.UnitDisc.neg_shift

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_zero : shift 0 = .refl 𝔻 := by
  ext z
  simp [coe_shift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_zero then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_zero ``Submission.Complex.UnitDisc.shift_zero

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_apply_zero (z : 𝔻) : shift z 0 = z := by simp [shift_eq_iff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_apply_zero then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_apply_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_apply_zero ``Submission.Complex.UnitDisc.shift_apply_zero

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_eq_zero_iff {z w : 𝔻} : shift z w = 0 ↔ w = -z := by
  rw [← Equiv.eq_symm_apply, symm_shift, shift_apply_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_eq_zero_iff then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_eq_zero_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_eq_zero_iff ``Submission.Complex.UnitDisc.shift_eq_zero_iff

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_apply_neg_self (z : 𝔻) : shift z (-z) = 0 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_apply_neg_self then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_apply_neg_self"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_apply_neg_self ``Submission.Complex.UnitDisc.shift_apply_neg_self

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_neg_apply_self (z : 𝔻) : shift (-z) z = 0 := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_neg_apply_self then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_neg_apply_self"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_neg_apply_self ``Submission.Complex.UnitDisc.shift_neg_apply_self

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_neg_apply_shift (z w : 𝔻) : shift (-z) (shift z w) = w := by
  rw [← symm_shift, Equiv.symm_apply_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_neg_apply_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_neg_apply_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_neg_apply_shift ``Submission.Complex.UnitDisc.shift_neg_apply_shift

open _root_.Complex _root_.Complex.UnitDisc in
@[simp]
theorem shift_apply_shift_neg (z w : 𝔻) : shift z (shift (-z) w) = w := by
  simpa using shift_neg_apply_shift (-z) w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_apply_shift_neg then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_apply_shift_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_apply_shift_neg ``Submission.Complex.UnitDisc.shift_apply_shift_neg

open _root_.Complex _root_.Complex.UnitDisc in
theorem neg_shift_neg (z w : 𝔻) : -z.shift (-w) = (-z).shift w := by
  rw [eq_comm, shift_eq_iff, _root_.Complex.UnitDisc.coe_neg, _root_.Complex.UnitDisc.coe_neg, coe_shift]
  field_simp (disch := apply shift_den_ne_zero')
  simp; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.neg_shift_neg then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.neg_shift_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.neg_shift_neg ``Submission.Complex.UnitDisc.neg_shift_neg

open _root_.Complex _root_.Complex.UnitDisc in
theorem involutive_shift_comp_neg (z : 𝔻) : (shift z <| -·).Involutive := by
  intro x
  simp [neg_shift_neg]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.involutive_shift_comp_neg then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.involutive_shift_comp_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.involutive_shift_comp_neg ``Submission.Complex.UnitDisc.involutive_shift_comp_neg

open _root_.Complex _root_.Complex.UnitDisc in
theorem norm_shift_le (z w : 𝔻) :
    ‖(z.shift w : ℂ)‖ ≤ (‖(z : ℂ)‖ + ‖(w : ℂ)‖) / (1 + ‖(z : ℂ)‖ * ‖(w : ℂ)‖) :=
  norm_shiftFun_le z w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.norm_shift_le then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.norm_shift_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.norm_shift_le ``Submission.Complex.UnitDisc.norm_shift_le

open _root_.Complex _root_.Complex.UnitDisc in
/-- A shift by `0` is the identity map, and all other shifts have no fixed points. -/
@[simp]
theorem shift_eq_self_iff {z w : 𝔻} : shift z w = w ↔ z = 0 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  suffices (z : ℂ) ≠ w * conj ↑z * w by
    simpa [shift_eq_iff, hz, add_comm (z : ℂ)] using this
  refine ne_of_apply_ne _root_.Norm.norm (ne_of_gt ?_)
  calc
    _ = ‖(z : ℂ)‖ * ‖(w : ℂ)‖ ^ 2 := by simp; ring
    _ < ‖(z : ℂ)‖ := mul_lt_of_lt_one_right (by simpa) <| by
      rw [← Complex.normSq_eq_norm_sq]; exact w.normSq_lt_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_eq_self_iff then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_eq_self_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_eq_self_iff ``Submission.Complex.UnitDisc.shift_eq_self_iff

open _root_.Complex _root_.Complex.UnitDisc in
lemma shift_apply_circle_smul (c : Circle) (z w : 𝔻) :
    shift z (c • w) = c • shift (c⁻¹ • z) w := by
  ext1
  simp only [coe_shift, _root_.Complex.UnitDisc.coe_circle_smul, ← mul_div_assoc, mul_add,
    map_mul, Circle.coe_inv_eq_conj, Complex.conj_conj, ← mul_assoc]
  rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
  simp [mul_comm (c : ℂ)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_apply_circle_smul then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_apply_circle_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_apply_circle_smul ``Submission.Complex.UnitDisc.shift_apply_circle_smul

open _root_.Complex _root_.Complex.UnitDisc in
/-- The composition of two shifts is a rotation by `shiftCompCoeff z w` composed with a shift. -/
@[simps! coe]
def shiftCompCoeff (z w : 𝔻) : Circle :=
  .ofConjDivSelf (1 + conj ↑z * w) (shift_den_ne_zero _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shiftCompCoeff then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shiftCompCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shiftCompCoeff ``Submission.Complex.UnitDisc.shiftCompCoeff

open _root_.Complex _root_.Complex.UnitDisc in
theorem shift_apply_shift (z w u : 𝔻) :
    shift z (shift w u) = shiftCompCoeff z w • shift (shift w z) u := by
  ext1
  have H₁ (z w u : 𝔻) : 1 + u * conj (w : ℂ) + (w + u) * conj (z : ℂ) ≠ 0 := by
    have := shift_den_ne_zero' (shift w u) z
    rw [coe_shift, div_mul_eq_mul_div₀, add_div_eq_mul_add_div, div_ne_zero_iff] at this
    · simpa [mul_comm] using this.left
    · apply shift_den_ne_zero
  have H₂ : 1 + w * conj (z : ℂ) + u * (conj ↑w + conj ↑z) ≠ 0 := by
    simpa [mul_comm] using H₁ (_root_.Star.star u) (_root_.Star.star w) (_root_.Star.star z)
  simp [coe_shift]
  field_simp
    (disch := first | apply shift_den_ne_zero | apply shift_den_ne_zero' | apply H₁ | exact H₂)
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_apply_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_apply_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_apply_shift ``Submission.Complex.UnitDisc.shift_apply_shift

open _root_.Complex _root_.Complex.UnitDisc in
theorem shift_trans_shift (z w : 𝔻) :
    (shift z).trans (shift w) =
      (shift (shift z w)).trans (MulAction.toPerm (shiftCompCoeff w z)) := by
  ext1 u
  simp [shift_apply_shift]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.UnitDisc.shift_trans_shift then
    throwError "Refusing to shadow existing declaration Complex.UnitDisc.shift_trans_shift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.UnitDisc.shift_trans_shift ``Submission.Complex.UnitDisc.shift_trans_shift

end

end UnitDisc

end Complex
