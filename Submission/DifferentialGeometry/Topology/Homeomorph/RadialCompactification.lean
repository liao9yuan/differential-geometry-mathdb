/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Homeomorph.Alexander
import Submission.DifferentialGeometry.Topology.Homeomorph.Conjugate
import Mathlib.Topology.OpenPartialHomeomorph.Composition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Filter _root_.Topology

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.OpenPartialHomeomorph in
private noncomputable def compress (x : E) : E := (2 / _root_.Max.max 2 (1 + ‖x‖)) • x

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.compress
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.compress target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private noncomputable def expand (x : E) : E := (_root_.Min.min 1 (2 - ‖x‖))⁻¹ • x

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.expand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.expand target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private theorem compress_eq_self {x : E} (hx : ‖x‖ ≤ 1) : compress x = x := by
  simp only [compress, max_eq_left (by linarith : 1 + ‖x‖ ≤ 2)]
  norm_num

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.compress_eq_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.compress_eq_self target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private theorem expand_eq_self {x : E} (hx : ‖x‖ ≤ 1) : expand x = x := by
  simp only [expand, min_eq_left (by linarith : 1 ≤ 2 - ‖x‖), inv_one, one_smul]

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.expand_eq_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.expand_eq_self target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private theorem norm_compress (x : E) :
    ‖compress x‖ = 2 * ‖x‖ / _root_.Max.max 2 (1 + ‖x‖) := by
  rw [compress, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  ring

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.norm_compress
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.norm_compress target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private theorem compress_mem_ball (x : E) : compress x ∈ _root_.Metric.ball (0 : E) 2 := by
  rw [_root_.Metric.mem_ball, dist_zero_right, norm_compress, div_lt_iff₀ (by positivity)]
  linarith [le_max_right (2 : ℝ) (1 + ‖x‖)]

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.compress_mem_ball
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.compress_mem_ball target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private theorem expand_compress (x : E) : expand (compress x) = x := by
  by_cases hx : ‖x‖ ≤ 1
  · rw [compress_eq_self hx, expand_eq_self hx]
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
    have hd : _root_.Max.max 2 (1 + ‖x‖) = 1 + ‖x‖ := max_eq_right (by linarith)
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have hn : ‖compress x‖ = 2 * ‖x‖ / (1 + ‖x‖) := by rw [norm_compress, hd]
    have hc : 1 < ‖compress x‖ := by
      rw [hn, lt_div_iff₀ hpos]
      linarith
    have he : 2 - ‖compress x‖ = 2 / (1 + ‖x‖) := by
      rw [hn]
      field_simp
      ring
    rw [expand, min_eq_right (by linarith : 2 - ‖compress x‖ ≤ 1), he,
      compress, hd, inv_smul_smul₀ (by positivity)]

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.expand_compress
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.expand_compress target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
private theorem compress_expand {x : E} (hx : x ∈ _root_.Metric.ball (0 : E) 2) :
    compress (expand x) = x := by
  have hx2 : ‖x‖ < 2 := mem_ball_zero_iff.mp hx
  by_cases hx1 : ‖x‖ ≤ 1
  · rw [expand_eq_self hx1, compress_eq_self hx1]
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx1
    have hp : 0 < 2 - ‖x‖ := sub_pos.mpr hx2
    have he : expand x = (2 - ‖x‖)⁻¹ • x := by
      rw [expand, min_eq_right (by linarith)]
    have hn : ‖expand x‖ = ‖x‖ / (2 - ‖x‖) := by
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
      ring
    have hg : 1 < ‖expand x‖ := by
      rw [hn, lt_div_iff₀ hp]
      linarith
    have hc : 2 / (1 + ‖expand x‖) = 2 - ‖x‖ := by
      rw [hn]
      field_simp
      ring
    rw [compress, max_eq_right (by linarith : 2 ≤ 1 + ‖expand x‖), hc,
      he, smul_inv_smul₀ hp.ne']

run_cmd do
  let target := ``Submission.OpenPartialHomeomorph.compress_expand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `OpenPartialHomeomorph.compress_expand target :: scope.openDecls } }

open _root_.OpenPartialHomeomorph in
noncomputable def radialCompression : OpenPartialHomeomorph E E where
  toFun := compress
  invFun := expand
  source := _root_.Set.univ
  target := _root_.Metric.ball 0 2
  map_source' x _ := compress_mem_ball x
  map_target' _ _ := _root_.Set.mem_univ _
  left_inv' x _ := expand_compress x
  right_inv' _ hx := compress_expand hx
  open_source := isOpen_univ
  open_target := _root_.Metric.isOpen_ball
  continuousOn_toFun := by
    apply Continuous.continuousOn
    exact (continuous_const.div (continuous_const.max (continuous_const.add continuous_norm))
      (fun x => ne_of_gt (by positivity : 0 < max 2 (1 + ‖x‖)))).smul continuous_id
  continuousOn_invFun := by
    apply ContinuousOn.smul _ continuousOn_id
    apply ContinuousOn.inv₀
      (continuous_const.min (continuous_const.sub continuous_norm)).continuousOn
    intro x hx
    have h := mem_ball_zero_iff.mp hx
    exact ne_of_gt (lt_min zero_lt_one (sub_pos.mpr h))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression ``Submission.OpenPartialHomeomorph.radialCompression

open _root_.OpenPartialHomeomorph in
@[simp]
theorem radialCompression_source : (radialCompression (E := E)).source = univ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression_source then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression_source"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression_source ``Submission.OpenPartialHomeomorph.radialCompression_source

open _root_.OpenPartialHomeomorph in
@[simp]
theorem radialCompression_target : (radialCompression (E := E)).target = _root_.Metric.ball 0 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression_target then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression_target"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression_target ``Submission.OpenPartialHomeomorph.radialCompression_target

open _root_.OpenPartialHomeomorph in
theorem radialCompression_apply (x : E) :
    radialCompression x = (2 / _root_.Max.max 2 (1 + ‖x‖)) • x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression_apply then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression_apply ``Submission.OpenPartialHomeomorph.radialCompression_apply

open _root_.OpenPartialHomeomorph in
theorem radialCompression_symm_apply (x : E) :
    radialCompression.symm x = (_root_.Min.min 1 (2 - ‖x‖))⁻¹ • x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression_symm_apply then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression_symm_apply ``Submission.OpenPartialHomeomorph.radialCompression_symm_apply

open _root_.OpenPartialHomeomorph in
theorem radialCompression_eq_self {x : E} (hx : ‖x‖ ≤ 1) :
    radialCompression x = x := compress_eq_self hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression_eq_self then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression_eq_self ``Submission.OpenPartialHomeomorph.radialCompression_eq_self

open _root_.OpenPartialHomeomorph in
theorem radialCompression_symm_eq_self {x : E} (hx : ‖x‖ ≤ 1) :
    radialCompression.symm x = x := expand_eq_self hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.radialCompression_symm_eq_self then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.radialCompression_symm_eq_self"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.radialCompression_symm_eq_self ``Submission.OpenPartialHomeomorph.radialCompression_symm_eq_self

open _root_.OpenPartialHomeomorph in
theorem norm_radialCompression_sub_le (x y : E) :
    ‖radialCompression x - radialCompression y‖ ≤
      4 / _root_.Max.max 2 (1 + ‖x‖) * ‖x - y‖ := by
  let p := _root_.Max.max 2 (1 + ‖x‖)
  let q := _root_.Max.max 2 (1 + ‖y‖)
  have hp : 0 < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hyq : ‖y‖ ≤ q := by dsimp [q]; linarith [le_max_right (2 : ℝ) (1 + ‖y‖)]
  have hd : |q - p| ≤ ‖x - y‖ := by
    have h := abs_max_sub_max_le_max (2 : ℝ) (1 + ‖y‖) 2 (1 + ‖x‖)
    have he : 1 + ‖y‖ - (1 + ‖x‖) = ‖y‖ - ‖x‖ := by ring
    rw [sub_self, abs_zero, he,
      show _root_.Max.max (0 : ℝ) |‖y‖ - ‖x‖| = |‖y‖ - ‖x‖| from max_eq_right (abs_nonneg _)] at h
    exact h.trans (by simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x)
  have heq : (2 / p) • x - (2 / q) • y =
      (2 / p) • (x - y) + (2 / p - 2 / q) • y := by
    rw [smul_sub, sub_smul]
    abel
  have habs : |2 / p - 2 / q| = 2 * |q - p| / (p * q) := by
    have he : 2 / p - 2 / q = 2 * (q - p) / (p * q) := by field_simp
    rw [he, abs_div, abs_mul, abs_of_pos (mul_pos hp hq)]
    norm_num
  change ‖(2 / p) • x - (2 / q) • y‖ ≤ 4 / p * ‖x - y‖
  rw [heq]
  calc
    _ ≤ ‖(2 / p) • (x - y)‖ + ‖(2 / p - 2 / q) • y‖ := norm_add_le _ _
    _ = (2 / p) * ‖x - y‖ + (2 * |q - p| / (p * q)) * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 2 / p), habs]
    _ ≤ (2 / p) * ‖x - y‖ + (2 * ‖x - y‖ / (p * q)) * q := by
      gcongr
    _ = 4 / p * ‖x - y‖ := by field_simp; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.norm_radialCompression_sub_le then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.norm_radialCompression_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.norm_radialCompression_sub_le ``Submission.OpenPartialHomeomorph.norm_radialCompression_sub_le

open _root_.OpenPartialHomeomorph in
theorem norm_radialCompression_conjugate_sub_le {f : E → E} {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) {x : E} (hx : x ∈ _root_.Metric.ball (0 : E) 2) (hx1 : 1 < ‖x‖) :
    ‖radialCompression (f (radialCompression.symm x)) - x‖ ≤ 2 * C * (2 - ‖x‖) := by
  have hp : 0 < 2 - ‖x‖ := sub_pos.mpr (mem_ball_zero_iff.mp hx)
  have hw : ‖radialCompression.symm x‖ = ‖x‖ / (2 - ‖x‖) := by
    rw [radialCompression_symm_apply, min_eq_right (by linarith), norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    ring
  have hw1 : 1 < ‖radialCompression.symm x‖ := by
    rw [hw, lt_div_iff₀ hp]
    linarith
  have hd : _root_.Max.max 2 (1 + ‖radialCompression.symm x‖) = 2 / (2 - ‖x‖) := by
    rw [max_eq_right (by linarith : 2 ≤ 1 + ‖radialCompression.symm x‖), hw]
    field_simp
    ring
  have h := norm_radialCompression_sub_le (radialCompression.symm x)
    (f (radialCompression.symm x))
  rw [(radialCompression (E := E)).right_inv hx, norm_sub_rev x] at h
  calc
    _ ≤ 4 / _root_.Max.max 2 (1 + ‖radialCompression.symm x‖) *
        ‖radialCompression.symm x - f (radialCompression.symm x)‖ := h
    _ ≤ 4 / _root_.Max.max 2 (1 + ‖radialCompression.symm x‖) * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [norm_sub_rev] using hf (radialCompression.symm x)
    _ = 2 * C * (2 - ‖x‖) := by rw [hd]; field_simp; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.norm_radialCompression_conjugate_sub_le then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.norm_radialCompression_conjugate_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.norm_radialCompression_conjugate_sub_le ``Submission.OpenPartialHomeomorph.norm_radialCompression_conjugate_sub_le

open _root_.OpenPartialHomeomorph in
theorem continuous_radialCompression_conjugateMap {f : E → E} (hf : Continuous f)
    {C : ℝ} (hbound : ∀ x, ‖f x - x‖ ≤ C) :
    Continuous ((radialCompression (E := E)).symm.conjugateMap f) := by
  let e := radialCompression (E := E)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbound 0)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ _root_.Metric.ball (0 : E) 2
  · have hh : ContinuousAt (fun y => e (f (e.symm y))) x :=
      (e.continuousAt (_root_.Set.mem_univ _)).comp
        (hf.continuousAt.comp (e.continuousAt_symm hx))
    apply hh.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact e.symm.conjugateMap_of_mem f hy
  · have hx2 : 2 ≤ ‖x‖ := by simpa only [_root_.Metric.mem_ball, dist_zero_right, not_lt] using hx
    have heq : e.symm.conjugateMap f x = x := e.symm.conjugateMap_of_notMem f hx
    have hopen : IsOpen {y : E | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have hnear : ∀ᶠ y in 𝓝 x, 1 < ‖y‖ := hopen.mem_nhds (by
      change 1 < ‖x‖
      linarith)
    have hb : _root_.Filter.Tendsto (fun y : E => 2 * C * _root_.Max.max 0 (2 - ‖y‖)) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun y : E => 2 * C * _root_.Max.max 0 (2 - ‖y‖)) :=
        continuous_const.mul (continuous_const.max (continuous_const.sub continuous_norm))
      simpa only [ContinuousAt, max_eq_left (by linarith : 2 - ‖x‖ ≤ 0), _root_.MulZeroClass.mul_zero] using
        hc.continuousAt (x := x)
    have hz : _root_.Filter.Tendsto (fun y : E => e.symm.conjugateMap f y - y) (𝓝 x) (𝓝 0) := by
      apply squeeze_zero_norm' _ hb
      filter_upwards [hnear] with y hy
      by_cases hy2 : y ∈ _root_.Metric.ball (0 : E) 2
      · rw [e.symm.conjugateMap_of_mem f hy2]
        exact (norm_radialCompression_conjugate_sub_le hbound hy2 hy).trans
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
      · rw [e.symm.conjugateMap_of_notMem f hy2, sub_self, norm_zero]
        positivity
    have hh := hz.add (continuous_id.continuousAt (x := x))
    change _root_.Filter.Tendsto (e.symm.conjugateMap f) (𝓝 x) (𝓝 (e.symm.conjugateMap f x))
    rw [heq]
    simpa only [sub_add_cancel, zero_add, id_eq] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.continuous_radialCompression_conjugateMap then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.continuous_radialCompression_conjugateMap"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.continuous_radialCompression_conjugateMap ``Submission.OpenPartialHomeomorph.continuous_radialCompression_conjugateMap

end OpenPartialHomeomorph

namespace Homeomorph
open _root_.Homeomorph

open _root_.OpenPartialHomeomorph (radialCompression)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open _root_.Homeomorph in
noncomputable def radialCompactification (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) : E ≃ₜ E := by
  let e := radialCompression (E := E)
  have hleft (g : E ≃ₜ E) :
      Function.LeftInverse (e.symm.conjugateMap g.symm) (e.symm.conjugateMap g) := by
    intro x
    by_cases hx : x ∈ e.target
    · rw [e.symm.conjugateMap_of_mem g hx, OpenPartialHomeomorph.symm_symm,
        e.symm.conjugateMap_of_mem g.symm (e.map_source (_root_.Set.mem_univ _)),
        OpenPartialHomeomorph.symm_symm]
      rw [e.left_inv (_root_.Set.mem_univ _), g.symm_apply_apply, e.right_inv hx]
    · rw [e.symm.conjugateMap_of_notMem g hx, e.symm.conjugateMap_of_notMem g.symm hx]
  have hi (x : E) : ‖f.symm x - x‖ ≤ C := by
    simpa only [f.apply_symm_apply, norm_sub_rev] using hf (f.symm x)
  exact {
    toFun := e.symm.conjugateMap f
    invFun := e.symm.conjugateMap f.symm
    left_inv := hleft f
    right_inv := hleft f.symm
    continuous_toFun := OpenPartialHomeomorph.continuous_radialCompression_conjugateMap
      f.continuous hf
    continuous_invFun := OpenPartialHomeomorph.continuous_radialCompression_conjugateMap
      f.symm.continuous hi }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.radialCompactification then
    throwError "Refusing to shadow existing declaration Homeomorph.radialCompactification"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.radialCompactification ``Submission.Homeomorph.radialCompactification

open _root_.Homeomorph in
theorem radialCompactification_apply (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) (x : E) :
    f.radialCompactification hf x = radialCompression.symm.conjugateMap f x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.radialCompactification_apply then
    throwError "Refusing to shadow existing declaration Homeomorph.radialCompactification_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.radialCompactification_apply ``Submission.Homeomorph.radialCompactification_apply

open _root_.Homeomorph in
theorem radialCompactification_symm_apply (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) (x : E) :
    (f.radialCompactification hf).symm x =
      radialCompression.symm.conjugateMap f.symm x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.radialCompactification_symm_apply then
    throwError "Refusing to shadow existing declaration Homeomorph.radialCompactification_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.radialCompactification_symm_apply ``Submission.Homeomorph.radialCompactification_symm_apply

open _root_.Homeomorph in
theorem radialCompactification_eqOn_compl (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) :
    _root_.Set.EqOn (f.radialCompactification hf) id (_root_.Metric.ball 0 2)ᶜ ∧
      EqOn (f.radialCompactification hf).symm id (_root_.Metric.ball 0 2)ᶜ :=
  ⟨fun _ hx => radialCompression.symm.conjugateMap_of_notMem f hx,
    fun _ hx => radialCompression.symm.conjugateMap_of_notMem f.symm hx⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.radialCompactification_eqOn_compl then
    throwError "Refusing to shadow existing declaration Homeomorph.radialCompactification_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.radialCompactification_eqOn_compl ``Submission.Homeomorph.radialCompactification_eqOn_compl

open _root_.Homeomorph in
theorem radialCompactification_apply_of_norm_le (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) {x : E} (hx : ‖x‖ ≤ 1) (hfx : ‖f x‖ ≤ 1) :
    f.radialCompactification hf x = f x := by
  rw [radialCompactification_apply,
    radialCompression.symm.conjugateMap_of_mem f (by
      change x ∈ _root_.Metric.ball (0 : E) 2
      rw [_root_.Metric.mem_ball, dist_zero_right]
      linarith)]
  rw [OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.radialCompression_symm_eq_self hx,
    OpenPartialHomeomorph.radialCompression_eq_self hfx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.radialCompactification_apply_of_norm_le then
    throwError "Refusing to shadow existing declaration Homeomorph.radialCompactification_apply_of_norm_le"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.radialCompactification_apply_of_norm_le ``Submission.Homeomorph.radialCompactification_apply_of_norm_le

open _root_.Homeomorph in
theorem radialCompactification_eventuallyEq (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) {x : E} (hx : ‖x‖ < 1) (hfx : ‖f x‖ < 1) :
    (f.radialCompactification hf : E → E) =ᶠ[𝓝 x] f := by
  have hU : IsOpen {y : E | ‖y‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hV : IsOpen {y : E | ‖f y‖ < 1} :=
    isOpen_lt f.continuous.norm continuous_const
  filter_upwards [hU.mem_nhds hx, hV.mem_nhds hfx] with y hy hfy
  exact f.radialCompactification_apply_of_norm_le hf hy.le hfy.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.radialCompactification_eventuallyEq then
    throwError "Refusing to shadow existing declaration Homeomorph.radialCompactification_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.radialCompactification_eventuallyEq ``Submission.Homeomorph.radialCompactification_eventuallyEq

open _root_.Homeomorph in
theorem exists_supported_isotopy_agreeing_of_bounded_displacement (f : E ≃ₜ E) {C : ℝ}
    (hf : ∀ x, ‖f x - x‖ ≤ C) :
    ∃ H : ℝ → E ≃ₜ E,
      Continuous (fun q : ℝ × E => H q.1 q.2) ∧
      Continuous (fun q : ℝ × E => (H q.1).symm q.2) ∧
      H 0 = Homeomorph.refl E ∧
      (∀ x, ‖x‖ ≤ 1 → ‖f x‖ ≤ 1 → H 1 x = f x) ∧
      (∀ t, _root_.Set.EqOn (H t) id (_root_.Metric.ball 0 2)ᶜ ∧ _root_.Set.EqOn (H t).symm id (_root_.Metric.ball 0 2)ᶜ) ∧
      (f 0 = 0 → (H 1 : E → E) =ᶠ[𝓝 0] f ∧ ∀ t, H t 0 = 0) := by
  let g := f.radialCompactification hf
  obtain ⟨H, hH, hHi, hH0, hH1, hfix, _, hzero⟩ :=
    g.alexander_trick (by norm_num : (0 : ℝ) ≤ 2) (f.radialCompactification_eqOn_compl hf).1
  refine ⟨H, hH, hHi, hH0, ?_, hfix, ?_⟩
  · intro x hx hfx
    rw [hH1]
    exact f.radialCompactification_apply_of_norm_le hf hx hfx
  · intro hf0
    have hg0 : g 0 = 0 := (f.radialCompactification_apply_of_norm_le hf
      (by simp) (by simp [hf0])).trans hf0
    refine ⟨?_, hzero hg0⟩
    rw [hH1]
    exact f.radialCompactification_eventuallyEq hf (by simp) (by simp [hf0])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Homeomorph.exists_supported_isotopy_agreeing_of_bounded_displacement then
    throwError "Refusing to shadow existing declaration Homeomorph.exists_supported_isotopy_agreeing_of_bounded_displacement"
  Lean.modifyEnv fun env => Lean.addAlias env `Homeomorph.exists_supported_isotopy_agreeing_of_bounded_displacement ``Submission.Homeomorph.exists_supported_isotopy_agreeing_of_bounded_displacement

end Homeomorph
