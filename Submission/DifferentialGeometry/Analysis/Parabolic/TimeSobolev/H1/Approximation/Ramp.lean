import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace timeH1

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
private theorem rampUp_smooth (T : ℝ) (z : X) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ (t / T) • z) (_root_.Set.Icc (0 : ℝ) T) :=
  ((contDiff_id.div_const T).smul_const z).contDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_smooth target :: scope.openDecls } }

omit [CompleteSpace X] in
private theorem rampDown_smooth (T : ℝ) (z : X) :
    ContDiffOn ℝ 1 (fun t : ℝ ↦ ((T - t) / T) • z) (_root_.Set.Icc (0 : ℝ) T) :=
  (((contDiff_const.sub contDiff_id).div_const T).smul_const z).contDiffOn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_smooth target :: scope.openDecls } }

noncomputable def rampUp (T : ℝ) (z : X) : timeH1 X T :=
  if hT : 0 ≤ T then
    ofContDiffOn hT (fun t : ℝ ↦ (t / T) • z) (rampUp_smooth T z)
  else
    0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp

noncomputable def rampDown (T : ℝ) (z : X) : timeH1 X T :=
  if hT : 0 ≤ T then
    ofContDiffOn hT (fun t : ℝ ↦ ((T - t) / T) • z) (rampDown_smooth T z)
  else
    0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown

theorem rampUp_apply {T t : ℝ} (hT : 0 ≤ T) (z : X)
    (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (rampUp T z).toFun t = (t / T) • z := by
  rw [rampUp, dif_pos hT]
  exact toFun_ofContDiffOn hT _ (rampUp_smooth T z) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_apply

theorem rampDown_apply {T t : ℝ} (hT : 0 ≤ T) (z : X)
    (ht : t ∈ _root_.Set.Icc (0 : ℝ) T) :
    (rampDown T z).toFun t = ((T - t) / T) • z := by
  rw [rampDown, dif_pos hT]
  exact toFun_ofContDiffOn hT _ (rampDown_smooth T z) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_apply

theorem rampUp_zero {T : ℝ} (hT : 0 < T) (z : X) :
    (rampUp T z).toFun 0 = 0 := by
  rw [rampUp_apply hT.le z ⟨le_rfl, hT.le⟩, zero_div, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_zero

theorem rampUp_end {T : ℝ} (hT : 0 < T) (z : X) :
    (rampUp T z).toFun T = z := by
  rw [rampUp_apply hT.le z ⟨hT.le, le_rfl⟩, div_self hT.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_end then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_end"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_end ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_end

theorem rampDown_zero {T : ℝ} (hT : 0 < T) (z : X) :
    (rampDown T z).toFun 0 = z := by
  rw [rampDown_apply hT.le z ⟨le_rfl, hT.le⟩, sub_zero,
    div_self hT.ne', one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_zero

theorem rampDown_end {T : ℝ} (hT : 0 < T) (z : X) :
    (rampDown T z).toFun T = 0 := by
  rw [rampDown_apply hT.le z ⟨hT.le, le_rfl⟩, sub_self, zero_div, zero_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_end then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_end"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_end ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_end

omit [CompleteSpace X] in
theorem rampUp_deriv {T : ℝ} (hT : 0 < T) (z : X) :
    (rampUp T z).deriv =ᵐ[timeMeasure T] fun _ ↦ (1 / T) • z := by
  rw [rampUp, dif_pos hT.le]
  filter_upwards [deriv_ofContDiffOn hT.le _ (rampUp_smooth T z)] with t ht
  rw [ht]
  exact (((hasDerivAt_id t).div_const T).smul_const z).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_deriv

omit [CompleteSpace X] in
theorem rampDown_deriv {T : ℝ} (hT : 0 < T) (z : X) :
    (rampDown T z).deriv =ᵐ[timeMeasure T] fun _ ↦ (-(1 / T)) • z := by
  rw [rampDown, dif_pos hT.le]
  filter_upwards [deriv_ofContDiffOn hT.le _ (rampDown_smooth T z)] with t ht
  rw [ht]
  simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div, one_div] using
    ((((hasDerivAt_const t T).sub (hasDerivAt_id t)).div_const T).smul_const z).deriv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_deriv ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_deriv

theorem rampUp_smul {T : ℝ} (hT : 0 < T) (c : ℝ) (z : X) :
    rampUp T (c • z) = c • rampUp T z := by
  apply timeH1.ext
  · rw [← toFun_zero (rampUp T (c • z)), initial_smul,
      ← toFun_zero (rampUp T z), rampUp_zero hT, rampUp_zero hT, smul_zero]
  · rw [deriv_smul]
    apply Lp.ext
    filter_upwards [rampUp_deriv hT (c • z), rampUp_deriv hT z,
      Lp.coeFn_smul c (rampUp T z).deriv] with t hcz hz hc
    rw [hcz, hc, Pi.smul_apply, hz]
    simp only [smul_smul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampUp_smul

theorem rampDown_smul {T : ℝ} (hT : 0 < T) (c : ℝ) (z : X) :
    rampDown T (c • z) = c • rampDown T z := by
  apply timeH1.ext
  · rw [← toFun_zero (rampDown T (c • z)), initial_smul,
      ← toFun_zero (rampDown T z), rampDown_zero hT, rampDown_zero hT]
  · rw [deriv_smul]
    apply Lp.ext
    filter_upwards [rampDown_deriv hT (c • z), rampDown_deriv hT z,
      Lp.coeFn_smul c (rampDown T z).deriv] with t hcz hz hc
    rw [hcz, hc, Pi.smul_apply, hz]
    simp only [smul_smul, mul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.timeH1.rampDown_smul

end timeH1

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
