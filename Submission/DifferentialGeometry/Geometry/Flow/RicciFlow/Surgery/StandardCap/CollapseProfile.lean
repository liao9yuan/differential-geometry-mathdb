import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalCoordinate
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.MeasureTheory
open scoped _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private def joinHeight (A : ℝ) : ℝ := -2 * A

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.joinHeight
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.joinHeight target :: scope.openDecls } }

private theorem smooth_radius_deriv : ContDiff ℝ ∞ (deriv conformalRadius) :=
  (contDiff_infty_iff_deriv.mp contDiff_conformalRadius).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_radius_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_radius_deriv target :: scope.openDecls } }

private theorem radius_speed (z : ℝ) :
    0 < deriv conformalRadius z ∧ deriv conformalRadius z ≤ 1 := by
  rw [deriv_conformalRadius]
  have hs : 0 < Real.sqrt 2 := by positivity
  exact ⟨div_pos (warpingFunction_pos (conformalRadius_pos z)) hs,
    (div_le_one hs).mpr (warpingFunction_le_sqrt_two _)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.radius_speed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.radius_speed target :: scope.openDecls } }

private def rightVelocity (A z : ℝ) : ℝ :=
  Real.smoothTransition (z - (joinHeight A - 1)) * deriv conformalRadius z

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity target :: scope.openDecls } }

private theorem smooth_rightVelocity (A : ℝ) : ContDiff ℝ ∞ (rightVelocity A) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    smooth_radius_deriv

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_rightVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_rightVelocity target :: scope.openDecls } }

private theorem rightVelocity_nonneg (A z : ℝ) : 0 ≤ rightVelocity A z :=
  mul_nonneg (Real.smoothTransition.nonneg _) (radius_speed z).1.le

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_nonneg target :: scope.openDecls } }

private theorem rightVelocity_le_deriv (A z : ℝ) :
    rightVelocity A z ≤ deriv conformalRadius z :=
  mul_le_of_le_one_left (radius_speed z).1.le (Real.smoothTransition.le_one _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_le_deriv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_le_deriv target :: scope.openDecls } }

private theorem rightVelocity_zero {A z : ℝ} (hz : z ≤ joinHeight A - 1) :
    rightVelocity A z = 0 := by
  rw [rightVelocity, Real.smoothTransition.zero_of_nonpos (by linarith), _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_zero target :: scope.openDecls } }

private theorem rightVelocity_tail {A z : ℝ} (hz : joinHeight A ≤ z) :
    rightVelocity A z = deriv conformalRadius z := by
  rw [rightVelocity, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_tail
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightVelocity_tail target :: scope.openDecls } }

private def rightMass (A : ℝ) : ℝ :=
  ∫ z in (joinHeight A - 1)..joinHeight A, rightVelocity A z

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightMass
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightMass target :: scope.openDecls } }

private def leftMass (A : ℝ) : ℝ := conformalRadius (joinHeight A) - rightMass A

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leftMass
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.leftMass target :: scope.openDecls } }

private theorem rightMass_nonneg (A : ℝ) : 0 ≤ rightMass A :=
  intervalIntegral.integral_nonneg_of_forall (by linarith) (rightVelocity_nonneg A)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightMass_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightMass_nonneg target :: scope.openDecls } }

private theorem rightMass_le (A : ℝ) :
    rightMass A ≤ conformalRadius (joinHeight A) - conformalRadius (joinHeight A - 1) := by
  have hftc : (∫ z in (joinHeight A - 1)..joinHeight A, deriv conformalRadius z) =
      conformalRadius (joinHeight A) - conformalRadius (joinHeight A - 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun z _ => (contDiff_conformalRadius.differentiable (by simp) z).hasDerivAt)
      (smooth_radius_deriv.continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _)
  exact (intervalIntegral.integral_mono_on (by linarith)
    ((smooth_rightVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _)
    (smooth_radius_deriv.continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _)
    (fun z _ => rightVelocity_le_deriv A z)).trans_eq hftc

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.rightMass_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.rightMass_le target :: scope.openDecls } }

private theorem leftMass_bounds (A : ℝ) :
    0 < leftMass A ∧ leftMass A ≤ conformalRadius (joinHeight A) := by
  have hlo := conformalRadius_pos (joinHeight A - 1)
  have hupper := rightMass_le A
  have hnonneg := rightMass_nonneg A
  dsimp [leftMass]
  constructor <;> linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leftMass_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.leftMass_bounds target :: scope.openDecls } }

def collapseTip (A : ℝ) : ℝ :=
  joinHeight A - 1 - 3 * leftMass A / 2 - (transitionEnd + 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip

private def leftVelocity (A z : ℝ) : ℝ :=
  Real.smoothTransition (1 - (z - collapseTip A - leftMass A / 2) / leftMass A)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity target :: scope.openDecls } }

private theorem smooth_leftVelocity (A : ℝ) : ContDiff ℝ ∞ (leftVelocity A) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (((contDiff_id.sub contDiff_const).sub contDiff_const).div_const _))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_leftVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_leftVelocity target :: scope.openDecls } }

private theorem leftVelocity_bounds (A z : ℝ) :
    0 ≤ leftVelocity A z ∧ leftVelocity A z ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity_bounds target :: scope.openDecls } }

private theorem leftVelocity_one {A z : ℝ}
    (hz : z ≤ collapseTip A + leftMass A / 2) : leftVelocity A z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hdiv : (z - collapseTip A - leftMass A / 2) / leftMass A ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (leftMass_bounds A).1.le
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity_one target :: scope.openDecls } }

private theorem leftVelocity_zero {A z : ℝ}
    (hz : collapseTip A + 3 * leftMass A / 2 ≤ z) : leftVelocity A z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hdiv : 1 ≤ (z - collapseTip A - leftMass A / 2) / leftMass A :=
    (le_div_iff₀ (leftMass_bounds A).1).mpr (by linarith)
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.leftVelocity_zero target :: scope.openDecls } }

private theorem left_end_lt_right_start (A : ℝ) :
    collapseTip A + 3 * leftMass A / 2 < joinHeight A - 1 := by
  unfold collapseTip
  linarith [transitionEnd_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.left_end_lt_right_start
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.left_end_lt_right_start target :: scope.openDecls } }

private theorem tip_lt_right_start (A : ℝ) : collapseTip A < joinHeight A - 1 := by
  have he := left_end_lt_right_start A
  linarith [(leftMass_bounds A).1]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.tip_lt_right_start
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.tip_lt_right_start target :: scope.openDecls } }

private def collapseVelocity (A z : ℝ) : ℝ := leftVelocity A z + rightVelocity A z

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity target :: scope.openDecls } }

private theorem smooth_collapseVelocity (A : ℝ) : ContDiff ℝ ∞ (collapseVelocity A) :=
  (smooth_leftVelocity A).add (smooth_rightVelocity A)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_collapseVelocity
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.smooth_collapseVelocity target :: scope.openDecls } }

private theorem collapseVelocity_bounds (A z : ℝ) :
    0 ≤ collapseVelocity A z ∧ collapseVelocity A z ≤ 1 := by
  refine ⟨add_nonneg (leftVelocity_bounds A z).1 (rightVelocity_nonneg A z), ?_⟩
  by_cases hz : z ≤ joinHeight A - 1
  · rw [collapseVelocity, rightVelocity_zero hz, add_zero]
    exact (leftVelocity_bounds A z).2
  · rw [collapseVelocity, leftVelocity_zero ((left_end_lt_right_start A).le.trans
      (not_le.mp hz).le), zero_add]
    exact (rightVelocity_le_deriv A z).trans (radius_speed z).2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity_bounds target :: scope.openDecls } }

private theorem collapseVelocity_initial {A z : ℝ}
    (hz : z ≤ collapseTip A + leftMass A / 2) : collapseVelocity A z = 1 := by
  have hright : z ≤ joinHeight A - 1 := by
    have he := left_end_lt_right_start A
    linarith [(leftMass_bounds A).1]
  rw [collapseVelocity, leftVelocity_one hz, rightVelocity_zero hright, add_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity_initial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity_initial target :: scope.openDecls } }

private theorem collapseVelocity_tail {A z : ℝ} (hz : joinHeight A ≤ z) :
    collapseVelocity A z = deriv conformalRadius z := by
  rw [collapseVelocity, rightVelocity_tail hz, leftVelocity_zero, zero_add]
  exact (left_end_lt_right_start A).le.trans (by linarith)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity_tail
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseVelocity_tail target :: scope.openDecls } }

private theorem integral_leftVelocity_transition (A : ℝ) :
    (∫ z in (collapseTip A + leftMass A / 2)..(collapseTip A + 3 * leftMass A / 2),
      leftVelocity A z) = leftMass A / 2 := by
  let f : ℝ → ℝ := fun u => Real.smoothTransition (1 - u)
  have hsub := intervalIntegral.integral_comp_sub_right
    (fun u => f (u / leftMass A)) (collapseTip A + leftMass A / 2)
    (a := collapseTip A + leftMass A / 2)
    (b := collapseTip A + 3 * leftMass A / 2)
  have harg : collapseTip A + 3 * leftMass A / 2 -
      (collapseTip A + leftMass A / 2) = leftMass A := by ring
  rw [sub_self, harg, intervalIntegral.integral_comp_div f (leftMass_bounds A).1.ne',
    zero_div, div_self (leftMass_bounds A).1.ne'] at hsub
  change (∫ z in (collapseTip A + leftMass A / 2)..(collapseTip A + 3 * leftMass A / 2),
      f ((z - collapseTip A - leftMass A / 2) / leftMass A)) = _
  simp_rw [sub_sub]
  rw [hsub]
  change leftMass A * (∫ u in (0 : ℝ)..1, Real.smoothTransition (1 - u)) = _
  rw [DifferentialGeometry.Analysis.integral_smoothTransition_one_sub]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_leftVelocity_transition
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_leftVelocity_transition target :: scope.openDecls } }

private theorem integral_leftVelocity_to_join (A : ℝ) :
    (∫ z in (collapseTip A)..joinHeight A, leftVelocity A z) = leftMass A := by
  have hi (a b : ℝ) := (smooth_leftVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) a b
  have hfirst : (∫ z in (collapseTip A)..(collapseTip A + leftMass A / 2),
      leftVelocity A z) = leftMass A / 2 := by
    calc
      _ = ∫ _ in (collapseTip A)..(collapseTip A + leftMass A / 2), (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [_root_.Set.uIcc_of_le (by linarith [(leftMass_bounds A).1])] at hz
        exact leftVelocity_one hz.2
      _ = _ := by simp
  have hlast : (∫ z in (collapseTip A + 3 * leftMass A / 2)..joinHeight A,
      leftVelocity A z) = 0 := by
    calc
      _ = ∫ _ in (collapseTip A + 3 * leftMass A / 2)..joinHeight A, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [_root_.Set.uIcc_of_le (by linarith [left_end_lt_right_start A])] at hz
        exact leftVelocity_zero hz.1
      _ = 0 := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hi (collapseTip A) (collapseTip A + leftMass A / 2))
    (hi (collapseTip A + leftMass A / 2) (collapseTip A + 3 * leftMass A / 2))
  have hsum' := intervalIntegral.integral_add_adjacent_intervals
    (hi (collapseTip A) (collapseTip A + 3 * leftMass A / 2))
    (hi (collapseTip A + 3 * leftMass A / 2) (joinHeight A))
  rw [hfirst, integral_leftVelocity_transition] at hsum
  rw [← hsum, hlast] at hsum'
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_leftVelocity_to_join
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_leftVelocity_to_join target :: scope.openDecls } }

private theorem integral_rightVelocity_to_join (A : ℝ) :
    (∫ z in (collapseTip A)..joinHeight A, rightVelocity A z) = rightMass A := by
  have hz : (∫ z in (collapseTip A)..(joinHeight A - 1), rightVelocity A z) = 0 := by
    calc
      _ = ∫ _ in (collapseTip A)..(joinHeight A - 1), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [_root_.Set.uIcc_of_le (tip_lt_right_start A).le] at hz
        exact rightVelocity_zero hz.2
      _ = 0 := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    ((smooth_rightVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) (collapseTip A) (joinHeight A - 1))
    ((smooth_rightVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) (joinHeight A - 1) (joinHeight A))
  rw [hz, zero_add] at hsum
  exact hsum.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_rightVelocity_to_join
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_rightVelocity_to_join target :: scope.openDecls } }

private theorem integral_collapseVelocity_to_join (A : ℝ) :
    (∫ z in (collapseTip A)..joinHeight A, collapseVelocity A z) =
      conformalRadius (joinHeight A) := by
  change (∫ z in (collapseTip A)..joinHeight A,
    leftVelocity A z + rightVelocity A z) = _
  rw [intervalIntegral.integral_add
    ((smooth_leftVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _)
    ((smooth_rightVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _),
    integral_leftVelocity_to_join, integral_rightVelocity_to_join]
  simp [leftMass]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_collapseVelocity_to_join
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.integral_collapseVelocity_to_join target :: scope.openDecls } }

def collapseRadius (A z : ℝ) : ℝ := ∫ u in (collapseTip A)..z, collapseVelocity A u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius

private theorem hasDerivAt_collapseRadius (A z : ℝ) :
    HasDerivAt (collapseRadius A) (collapseVelocity A z) z :=
  intervalIntegral.integral_hasDerivAt_right
    ((smooth_collapseVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _)
    (smooth_collapseVelocity A).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (smooth_collapseVelocity A).continuous.continuousAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.hasDerivAt_collapseRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.hasDerivAt_collapseRadius target :: scope.openDecls } }

private theorem deriv_collapseRadius (A z : ℝ) :
    deriv (collapseRadius A) z = collapseVelocity A z :=
  (hasDerivAt_collapseRadius A z).deriv

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_collapseRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_collapseRadius target :: scope.openDecls } }

theorem contDiff_collapseRadius (A : ℝ) : ContDiff ℝ ∞ (collapseRadius A) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun z => (hasDerivAt_collapseRadius A z).differentiableAt, ?_⟩
  have h : deriv (collapseRadius A) = collapseVelocity A := funext (deriv_collapseRadius A)
  rw [h]
  exact smooth_collapseVelocity A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_collapseRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_collapseRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_collapseRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.contDiff_collapseRadius

theorem deriv_collapseRadius_mem_Icc (A z : ℝ) :
    deriv (collapseRadius A) z ∈ _root_.Set.Icc (0 : ℝ) 1 := by
  rw [deriv_collapseRadius]
  exact collapseVelocity_bounds A z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_collapseRadius_mem_Icc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_collapseRadius_mem_Icc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_collapseRadius_mem_Icc ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.deriv_collapseRadius_mem_Icc

theorem monotone_collapseRadius (A : ℝ) : Monotone (collapseRadius A) :=
  monotone_of_deriv_nonneg (fun z => (hasDerivAt_collapseRadius A z).differentiableAt)
    (fun z => (deriv_collapseRadius_mem_Icc A z).1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.monotone_collapseRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.monotone_collapseRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.monotone_collapseRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.monotone_collapseRadius

theorem lipschitzWith_collapseRadius (A : ℝ) : LipschitzWith 1 (collapseRadius A) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun z => (hasDerivAt_collapseRadius A z).differentiableAt)
  intro z
  change ‖deriv (collapseRadius A) z‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs, abs_of_nonneg (deriv_collapseRadius_mem_Icc A z).1]
  exact (deriv_collapseRadius_mem_Icc A z).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.lipschitzWith_collapseRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.lipschitzWith_collapseRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.lipschitzWith_collapseRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.lipschitzWith_collapseRadius

@[simp] theorem collapseRadius_tip (A : ℝ) : collapseRadius A (collapseTip A) = 0 := by
  simp [collapseRadius]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_tip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_tip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_tip ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_tip

theorem collapseRadius_linear_germ (A : ℝ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ z : ℝ, z ≤ collapseTip A + σ →
      collapseRadius A z = z - collapseTip A := by
  refine ⟨leftMass A / 2, div_pos (leftMass_bounds A).1 (by norm_num), ?_⟩
  intro z hz
  calc
    _ = ∫ _ in (collapseTip A)..z, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply collapseVelocity_initial
      exact hu.2.trans (max_le (by linarith [(leftMass_bounds A).1]) hz)
    _ = _ := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_linear_germ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_linear_germ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_linear_germ ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_linear_germ

theorem collapseRadius_pos_iff {A z : ℝ} :
    0 < collapseRadius A z ↔ collapseTip A < z := by
  constructor
  · intro hz
    by_contra hn
    have hm := monotone_collapseRadius A (not_lt.mp hn)
    rw [collapseRadius_tip] at hm
    exact (not_lt_of_ge hm) hz
  · intro hz
    obtain ⟨σ, hσ, hlin⟩ := collapseRadius_linear_germ A
    let s := _root_.Min.min σ (z - collapseTip A) / 2
    have hs : 0 < s := div_pos (lt_min hσ (sub_pos.mpr hz)) (by norm_num)
    have hσle := min_le_left σ (z - collapseTip A)
    have hzle := min_le_right σ (z - collapseTip A)
    have hvalue : collapseRadius A (collapseTip A + s) = s := by
      simpa only [add_sub_cancel_left] using hlin (collapseTip A + s) (by dsimp [s]; linarith)
    have hmono := monotone_collapseRadius A (show collapseTip A + s ≤ z by dsimp [s]; linarith)
    rw [hvalue] at hmono
    exact hs.trans_le hmono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_pos_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_pos_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_pos_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_pos_iff

theorem collapseRadius_eq_conformalRadius {A z : ℝ} (hz : -2 * A ≤ z) :
    collapseRadius A z = conformalRadius z := by
  have htail : (∫ u in (joinHeight A)..z, collapseVelocity A u) =
      conformalRadius z - conformalRadius (joinHeight A) := by
    calc
      _ = ∫ u in (joinHeight A)..z, deriv conformalRadius u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [_root_.Set.uIcc_of_le (show joinHeight A ≤ z from hz)] at hu
        exact collapseVelocity_tail hu.1
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => (contDiff_conformalRadius.differentiable (by simp) u).hasDerivAt)
        (smooth_radius_deriv.continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) _ _)
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    ((smooth_collapseVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) (collapseTip A) (joinHeight A))
    ((smooth_collapseVelocity A).continuous.intervalIntegrable (μ := _root_.MeasureTheory.MeasureSpace.volume) (joinHeight A) z)
  rw [integral_collapseVelocity_to_join, htail] at hsum
  dsimp [collapseRadius]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_eq_conformalRadius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_eq_conformalRadius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_eq_conformalRadius ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_eq_conformalRadius

theorem collapseTip_lt (A : ℝ) : collapseTip A < -2 * A - transitionEnd := by
  dsimp [collapseTip, joinHeight]
  linarith [(leftMass_bounds A).1]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lt

theorem collapseRadius_zero {A : ℝ} (hA : 0 < A) : collapseRadius A 0 = transitionEnd := by
  rw [collapseRadius_eq_conformalRadius (by linarith), conformalRadius_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_zero

theorem collapseRadius_mapsTo {A : ℝ} (hA : 0 < A) :
    MapsTo (collapseRadius A) (_root_.Set.Icc (collapseTip A) 0) (_root_.Set.Icc 0 transitionEnd) := by
  intro z hz
  constructor
  · simpa only [collapseRadius_tip] using monotone_collapseRadius A hz.1
  · simpa only [collapseRadius_zero hA] using monotone_collapseRadius A hz.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_mapsTo ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseRadius_mapsTo

theorem collapseTip_lower_bound {A : ℝ} (hA : 0 < A) :
    -(2 * A + 5 * transitionEnd / 2 + 3) < collapseTip A := by
  have hm := (leftMass_bounds A).2
  have hr : conformalRadius (joinHeight A) ≤ transitionEnd := by
    simpa only [conformalRadius_zero] using
      strictMono_conformalRadius.monotone (show joinHeight A ≤ 0 by dsimp [joinHeight]; linarith)
  dsimp [collapseTip, joinHeight]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lower_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_lower_bound

theorem collapseTip_mem_buffer {A δ : ℝ} (hA : 0 < A) (hδ : 0 < δ)
    (hsmall : δ ≤ (2 * A + 5 * transitionEnd / 2 + 3)⁻¹) :
    collapseTip A ∈ _root_.Set.Ioo (-(δ⁻¹)) (-2 * A - transitionEnd) := by
  have hM : 0 < 2 * A + 5 * transitionEnd / 2 + 3 := by linarith [transitionEnd_pos]
  have hi := (inv_le_inv₀ (inv_pos.mpr hM) hδ).mpr hsmall
  rw [inv_inv] at hi
  exact ⟨(neg_le_neg hi).trans_lt (collapseTip_lower_bound hA), collapseTip_lt A⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_mem_buffer then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_mem_buffer"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_mem_buffer ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.collapseTip_mem_buffer

end DifferentialGeometry.PDE.RicciFlow.StandardCap
