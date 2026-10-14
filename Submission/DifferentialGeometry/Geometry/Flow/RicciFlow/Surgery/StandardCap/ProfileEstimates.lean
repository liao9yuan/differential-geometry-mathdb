import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Profile

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private theorem sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sqrt_two_ne_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.sqrt_two_ne_zero target :: scope.openDecls } }

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sqrt_two_sq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.sqrt_two_sq target :: scope.openDecls } }

private theorem sin_angle_pos {r : ℝ} (hr : 0 < r) : 0 < Real.sin (angle r) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos hr)
    ((angle_le_pi_div_two r).trans_lt (half_lt_self Real.pi_pos))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sin_angle_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.sin_angle_pos target :: scope.openDecls } }

theorem neg_deriv_deriv_warpingFunction_div_eq_angle {r : ℝ} (hr : 0 < r) :
    -deriv (deriv warpingFunction) r / warpingFunction r =
      (deriv angle r) ^ 2 -
        Real.cot (angle r) * deriv (deriv angle) r := by
  rw [deriv_deriv_warpingFunction, warpingFunction, Real.cot_eq_cos_div_sin]
  have hsin := (sin_angle_pos hr).ne'
  field_simp [sqrt_two_ne_zero]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_angle

theorem one_sub_deriv_warpingFunction_sq_div_eq_angle (r : ℝ) :
    (1 - (deriv warpingFunction r) ^ 2) / (warpingFunction r) ^ 2 =
      (1 - 2 * (Real.cos (angle r)) ^ 2 * (deriv angle r) ^ 2) /
        (2 * (Real.sin (angle r)) ^ 2) := by
  rw [deriv_warpingFunction, warpingFunction]
  simp only [mul_pow, sqrt_two_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_angle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_angle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_angle ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_angle

theorem neg_deriv_deriv_warpingFunction_div_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ -deriv (deriv warpingFunction) r / warpingFunction r :=
  div_nonneg (neg_nonneg.mpr (deriv_deriv_warpingFunction_nonpos hr.le))
    (warpingFunction_pos hr).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_nonneg

private theorem deriv_angle_sq_le_half (r : ℝ) : (deriv angle r) ^ 2 ≤ 1 / 2 := by
  have hbound := pow_le_pow_left₀ (deriv_angle_nonneg r) (deriv_angle_le r) 2
  have hsq : (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, one_pow, sqrt_two_sq]
  exact hbound.trans_eq hsq

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_sq_le_half
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_sq_le_half target :: scope.openDecls } }

theorem deriv_warpingFunction_sq_add_half_sq_le_one (r : ℝ) :
    (deriv warpingFunction r) ^ 2 + (warpingFunction r) ^ 2 / 2 ≤ 1 := by
  rw [deriv_warpingFunction, warpingFunction]
  simp only [mul_pow, sqrt_two_sq]
  have hprod := mul_le_mul_of_nonneg_left (deriv_angle_sq_le_half r)
    (show 0 ≤ 2 * (Real.cos (angle r)) ^ 2 by positivity)
  nlinarith [Real.sin_sq_add_cos_sq (angle r)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_sq_add_half_sq_le_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_sq_add_half_sq_le_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_sq_add_half_sq_le_one ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_sq_add_half_sq_le_one

theorem half_le_one_sub_deriv_warpingFunction_sq_div {r : ℝ} (hr : 0 < r) :
    1 / 2 ≤ (1 - (deriv warpingFunction r) ^ 2) / (warpingFunction r) ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (warpingFunction_pos hr))).mpr
  linarith [deriv_warpingFunction_sq_add_half_sq_le_one r]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_one_sub_deriv_warpingFunction_sq_div then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_one_sub_deriv_warpingFunction_sq_div"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_one_sub_deriv_warpingFunction_sq_div ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_one_sub_deriv_warpingFunction_sq_div

theorem one_le_warpingFunction_derivative_combination {r : ℝ} (hr : 0 < r) :
    1 ≤ 4 * (-deriv (deriv warpingFunction) r / warpingFunction r) +
      2 * ((1 - (deriv warpingFunction r) ^ 2) / (warpingFunction r) ^ 2) := by
  linarith [neg_deriv_deriv_warpingFunction_div_nonneg hr,
    half_le_one_sub_deriv_warpingFunction_sq_div hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_warpingFunction_derivative_combination then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_warpingFunction_derivative_combination"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_warpingFunction_derivative_combination ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.one_le_warpingFunction_derivative_combination

theorem deriv_angle_eq_of_le_transitionStart {r : ℝ} (hr : r ≤ transitionStart) :
    deriv angle r = 1 / Real.sqrt 2 := by
  rw [deriv_angle, Real.smoothTransition.one_of_one_le, mul_one]
  dsimp only [transitionEnd]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_of_le_transitionStart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_of_le_transitionStart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_of_le_transitionStart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_of_le_transitionStart

theorem deriv_deriv_angle_eq_zero_of_lt_transitionStart {r : ℝ} (hr : r < transitionStart) :
    deriv (deriv angle) r = 0 := by
  have heq : deriv angle =ᶠ[𝓝 r] fun _ => 1 / Real.sqrt 2 := by
    filter_upwards [eventually_lt_nhds hr] with x hx
    exact deriv_angle_eq_of_le_transitionStart hx.le
  rw [heq.deriv_eq, deriv_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_angle_eq_zero_of_lt_transitionStart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_angle_eq_zero_of_lt_transitionStart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_angle_eq_zero_of_lt_transitionStart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_angle_eq_zero_of_lt_transitionStart

theorem neg_deriv_deriv_warpingFunction_div_eq_half_of_lt_transitionStart
    {r : ℝ} (hr : 0 < r) (hround : r < transitionStart) :
    -deriv (deriv warpingFunction) r / warpingFunction r = 1 / 2 := by
  rw [neg_deriv_deriv_warpingFunction_div_eq_angle hr,
    deriv_angle_eq_of_le_transitionStart hround.le,
    deriv_deriv_angle_eq_zero_of_lt_transitionStart hround,
    _root_.MulZeroClass.mul_zero, sub_zero, div_pow, one_pow, sqrt_two_sq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_half_of_lt_transitionStart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_half_of_lt_transitionStart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_half_of_lt_transitionStart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_half_of_lt_transitionStart

theorem one_sub_deriv_warpingFunction_sq_div_eq_half_of_lt_transitionStart
    {r : ℝ} (hr : 0 < r) (hround : r < transitionStart) :
    (1 - (deriv warpingFunction r) ^ 2) / (warpingFunction r) ^ 2 = 1 / 2 := by
  rw [one_sub_deriv_warpingFunction_sq_div_eq_angle,
    deriv_angle_eq_of_le_transitionStart hround.le,
    div_pow, one_pow, sqrt_two_sq]
  have hsin := (sin_angle_pos hr).ne'
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq (angle r)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_lt_transitionStart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_lt_transitionStart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_lt_transitionStart ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_lt_transitionStart

theorem deriv_angle_eq_zero_of_transitionEnd_le {r : ℝ} (hr : transitionEnd ≤ r) :
    deriv angle r = 0 := by
  rw [deriv_angle, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr), _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_zero_of_transitionEnd_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_zero_of_transitionEnd_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_zero_of_transitionEnd_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_angle_eq_zero_of_transitionEnd_le

theorem deriv_warpingFunction_eq_zero_of_transitionEnd_le {r : ℝ} (hr : transitionEnd ≤ r) :
    deriv warpingFunction r = 0 := by
  rw [deriv_warpingFunction, deriv_angle_eq_zero_of_transitionEnd_le hr, _root_.MulZeroClass.mul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_eq_zero_of_transitionEnd_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_eq_zero_of_transitionEnd_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_eq_zero_of_transitionEnd_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_warpingFunction_eq_zero_of_transitionEnd_le

theorem deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le
    {r : ℝ} (hr : transitionEnd ≤ r) :
    deriv (deriv warpingFunction) r = 0 := by
  rw [deriv_deriv_warpingFunction, angle_eq_pi_div_two hr,
    deriv_angle_eq_zero_of_transitionEnd_le hr, Real.cos_pi_div_two]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le

theorem neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le
    {r : ℝ} (hr : transitionEnd ≤ r) :
    -deriv (deriv warpingFunction) r / warpingFunction r = 0 := by
  rw [deriv_deriv_warpingFunction_eq_zero_of_transitionEnd_le hr]
  simp only [neg_zero, zero_div]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le

theorem one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le
    {r : ℝ} (hr : transitionEnd ≤ r) :
    (1 - (deriv warpingFunction r) ^ 2) / (warpingFunction r) ^ 2 = 1 / 2 := by
  rw [deriv_warpingFunction_eq_zero_of_transitionEnd_le hr,
    warpingFunction_eq_sqrt_two hr, sqrt_two_sq]
  norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
