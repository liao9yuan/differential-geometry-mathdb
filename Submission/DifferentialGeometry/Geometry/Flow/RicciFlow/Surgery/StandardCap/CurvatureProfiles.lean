import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.ContDiff _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.InnerProductSpace
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

def radialSectionalValue (r : ℝ) : ℝ :=
  if r ≤ 0 then 1 / 2 else -deriv (deriv warpingFunction) r / warpingFunction r

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue

def tangentialSectionalValue (r : ℝ) : ℝ :=
  if r ≤ 0 then 1 / 2 else (1 - deriv warpingFunction r ^ 2) / warpingFunction r ^ 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue

theorem radialSectionalValue_of_pos {r : ℝ} (hr : 0 < r) :
    radialSectionalValue r = -deriv (deriv warpingFunction) r / warpingFunction r := by
  simp only [radialSectionalValue, not_le_of_gt hr, ↓reduceIte]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_of_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_of_pos

theorem tangentialSectionalValue_of_pos {r : ℝ} (hr : 0 < r) :
    tangentialSectionalValue r = (1 - deriv warpingFunction r ^ 2) / warpingFunction r ^ 2 := by
  simp only [tangentialSectionalValue, not_le_of_gt hr, ↓reduceIte]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_of_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_of_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_of_pos

theorem radialSectionalValue_round {r : ℝ} (hr : r < transitionStart) :
    radialSectionalValue r = 1 / 2 := by
  by_cases h0 : r ≤ 0
  · simp [radialSectionalValue, h0]
  · rw [radialSectionalValue_of_pos (lt_of_not_ge h0)]
    exact neg_deriv_deriv_warpingFunction_div_eq_half_of_lt_transitionStart (lt_of_not_ge h0) hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_round then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_round"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_round ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_round

theorem tangentialSectionalValue_round {r : ℝ} (hr : r < transitionStart) :
    tangentialSectionalValue r = 1 / 2 := by
  by_cases h0 : r ≤ 0
  · simp [tangentialSectionalValue, h0]
  · rw [tangentialSectionalValue_of_pos (lt_of_not_ge h0)]
    exact one_sub_deriv_warpingFunction_sq_div_eq_half_of_lt_transitionStart (lt_of_not_ge h0) hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_round then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_round"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_round ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_round

theorem contDiff_radialSectionalValue : ContDiff ℝ ∞ radialSectionalValue := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r < transitionStart
  · apply (contDiffAt_const (c := (1 / 2 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with y hy
    exact radialSectionalValue_round hy
  · have h0 : 0 < r := transitionStart_pos.trans_le (le_of_not_gt hr)
    have ha := (warpingFunction_pos h0).ne'
    have hder : ContDiffAt ℝ ∞ (deriv (deriv warpingFunction)) r :=
      ((contDiff_warpingFunction.deriv' (n := ∞)).deriv' (n := ∞)).contDiffAt
    apply (hder.neg.div contDiff_warpingFunction.contDiffAt ha).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h0] with y hy
    exact radialSectionalValue_of_pos hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_radialSectionalValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_radialSectionalValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_radialSectionalValue ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_radialSectionalValue

theorem contDiff_tangentialSectionalValue : ContDiff ℝ ∞ tangentialSectionalValue := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r < transitionStart
  · apply (contDiffAt_const (c := (1 / 2 : ℝ))).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with y hy
    exact tangentialSectionalValue_round hy
  · have h0 : 0 < r := transitionStart_pos.trans_le (le_of_not_gt hr)
    have ha := pow_ne_zero 2 (warpingFunction_pos h0).ne'
    have hder : ContDiffAt ℝ ∞ (deriv warpingFunction) r :=
      (contDiff_warpingFunction.deriv' (n := ∞)).contDiffAt
    apply (((contDiffAt_const (c := (1 : ℝ))).sub (hder.pow 2)).div
      (contDiff_warpingFunction.contDiffAt.pow 2) ha).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds h0] with y hy
    exact tangentialSectionalValue_of_pos hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_tangentialSectionalValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_tangentialSectionalValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_tangentialSectionalValue ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_tangentialSectionalValue

theorem sectionalCurvature_radial_eq_profile {x v : E3} (hx : x ≠ 0)
    (hv : v ≠ 0) (hxv : ⟪x, v⟫_ℝ = 0) :
    sectionalCurvature metric x x v = radialSectionalValue ‖x‖ :=
  (sectionalCurvature_radial hx hv hxv).trans
    (radialSectionalValue_of_pos (norm_pos_iff.mpr hx)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_eq_profile then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_eq_profile"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_eq_profile ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_radial_eq_profile

theorem sectionalCurvature_tangential_eq_profile {x v w : E3} (hx : x ≠ 0)
    (hv : ⟪x, v⟫_ℝ = 0) (hw : ⟪x, w⟫_ℝ = 0)
    (hvw : ‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2 ≠ 0) :
    sectionalCurvature metric x v w = tangentialSectionalValue ‖x‖ :=
  (sectionalCurvature_tangential hx hv hw hvw).trans
    (tangentialSectionalValue_of_pos (norm_pos_iff.mpr hx)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_tangential_eq_profile then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_tangential_eq_profile"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_tangential_eq_profile ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.sectionalCurvature_tangential_eq_profile

theorem metricScalarAt_eq_profiles (x : E3) :
    metricScalarAt metric x = 4 * radialSectionalValue ‖x‖ + 2 * tangentialSectionalValue ‖x‖ := by
  by_cases hx : x = 0
  · subst x
    rw [metricScalarAt_zero]
    norm_num [radialSectionalValue, tangentialSectionalValue]
  · rw [radialSectionalValue_of_pos (norm_pos_iff.mpr hx),
      tangentialSectionalValue_of_pos (norm_pos_iff.mpr hx)]
    exact metricScalarAt_eq_warping hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_profiles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_profiles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_profiles ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.metricScalarAt_eq_profiles

@[simp] theorem radialSectionalValue_zero : radialSectionalValue 0 = 1 / 2 := by
  simp [radialSectionalValue]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_zero

@[simp] theorem tangentialSectionalValue_zero : tangentialSectionalValue 0 = 1 / 2 := by
  simp [tangentialSectionalValue]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_zero

theorem radialSectionalValue_nonneg (r : ℝ) : 0 ≤ radialSectionalValue r := by
  by_cases hr : r ≤ 0
  · norm_num [radialSectionalValue, hr]
  · rw [radialSectionalValue_of_pos (lt_of_not_ge hr)]
    exact neg_deriv_deriv_warpingFunction_div_nonneg (lt_of_not_ge hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_nonneg

theorem half_le_tangentialSectionalValue (r : ℝ) : 1 / 2 ≤ tangentialSectionalValue r := by
  by_cases hr : r ≤ 0
  · simp [tangentialSectionalValue, hr]
  · rw [tangentialSectionalValue_of_pos (lt_of_not_ge hr)]
    exact half_le_one_sub_deriv_warpingFunction_sq_div (lt_of_not_ge hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_tangentialSectionalValue then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_tangentialSectionalValue"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_tangentialSectionalValue ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.half_le_tangentialSectionalValue

theorem radialSectionalValue_cylindrical {r : ℝ} (hr : transitionEnd ≤ r) :
    radialSectionalValue r = 0 :=
  (radialSectionalValue_of_pos (transitionEnd_pos.trans_le hr)).trans
    (neg_deriv_deriv_warpingFunction_div_eq_zero_of_transitionEnd_le hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_cylindrical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_cylindrical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_cylindrical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radialSectionalValue_cylindrical

theorem tangentialSectionalValue_cylindrical {r : ℝ} (hr : transitionEnd ≤ r) :
    tangentialSectionalValue r = 1 / 2 :=
  (tangentialSectionalValue_of_pos (transitionEnd_pos.trans_le hr)).trans
    (one_sub_deriv_warpingFunction_sq_div_eq_half_of_transitionEnd_le hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_cylindrical then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_cylindrical"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_cylindrical ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.tangentialSectionalValue_cylindrical

end DifferentialGeometry.PDE.RicciFlow.StandardCap
