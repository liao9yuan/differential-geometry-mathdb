import Submission.DifferentialGeometry.Analysis.Complex.DiskAutomorphism.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ComplexConjugate _root_.ContDiff

namespace Complex
open _root_.Complex

open _root_.Complex in
def diskBoundaryArgumentLift (a η : ℂ) (t : ℝ) : ℝ :=
  t + _root_.Complex.arg η / (2 * Real.pi) - _root_.Complex.arg (1 - conj a * _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I)) / Real.pi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskBoundaryArgumentLift then
    throwError "Refusing to shadow existing declaration Complex.diskBoundaryArgumentLift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskBoundaryArgumentLift ``Submission.Complex.diskBoundaryArgumentLift

open _root_.Complex in
theorem contDiff_diskBoundaryArgumentLift {a : ℂ} (ha : ‖a‖ < 1) (η : ℂ) :
    ContDiff ℝ ∞ (diskBoundaryArgumentLift a η) := by
  have hf : ContDiff ℝ ∞ (fun t : ℝ => (1 : ℂ) - conj a * _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I)) := by
    have hreal : ContDiff ℝ ∞ (fun t : ℝ => 2 * Real.pi * t) :=
      contDiff_const.mul contDiff_id
    have hce : ContDiff ℝ ∞ (fun t : ℝ => ((2 * Real.pi * t : ℝ) : ℂ) * _root_.Complex.I) :=
      (_root_.Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const
    exact contDiff_const.sub (contDiff_const.mul
      (((show ContDiff ℂ ∞ _root_.Complex.exp from _root_.Complex.contDiff_exp).restrict_scalars ℝ).comp hce))
  have hs (t : ℝ) : 1 - conj a * _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I) ∈ slitPlane := by
    apply _root_.Complex.mem_slitPlane_iff.mpr
    exact Or.inl (diskMoebius_denominator_re_pos ha (_root_.Complex.norm_exp_ofReal_mul_I _).le)
  have hl : ContDiff ℝ ∞ (fun t : ℝ => _root_.Complex.log (1 - conj a * _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact ((_root_.Complex.contDiffAt_log (n := ∞) (hs t)).restrict_scalars ℝ).comp t hf.contDiffAt
  have harg : ContDiff ℝ ∞ (fun t : ℝ => _root_.Complex.arg (1 - conj a * _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I))) := by
    simpa only [Function.comp_def, _root_.Complex.imCLM_apply, _root_.Complex.log_im] using _root_.Complex.imCLM.contDiff.comp hl
  exact (contDiff_id.add contDiff_const).sub (harg.div_const _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.contDiff_diskBoundaryArgumentLift then
    throwError "Refusing to shadow existing declaration Complex.contDiff_diskBoundaryArgumentLift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.contDiff_diskBoundaryArgumentLift ``Submission.Complex.contDiff_diskBoundaryArgumentLift

open _root_.Complex in
private theorem exp_period_one (t : ℝ) :
    exp ((2 * Real.pi * (t + 1) : ℝ) * _root_.Complex.I) = _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I) := by
  have h : ((2 * Real.pi * (t + 1) : ℝ) : ℂ) * _root_.Complex.I =
      ((2 * Real.pi * t : ℝ) : ℂ) * _root_.Complex.I + 2 * Real.pi * I := by push_cast; ring
  rw [h, _root_.Complex.exp_add, _root_.Complex.exp_two_pi_mul_I, mul_one]

run_cmd do
  let target := ``Submission.Complex.exp_period_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.exp_period_one target :: scope.openDecls } }

open _root_.Complex in
theorem diskBoundaryArgumentLift_add_one (a η : ℂ) (t : ℝ) :
    diskBoundaryArgumentLift a η (t + 1) = diskBoundaryArgumentLift a η t + 1 := by
  unfold diskBoundaryArgumentLift
  rw [exp_period_one]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.diskBoundaryArgumentLift_add_one then
    throwError "Refusing to shadow existing declaration Complex.diskBoundaryArgumentLift_add_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.diskBoundaryArgumentLift_add_one ``Submission.Complex.diskBoundaryArgumentLift_add_one

open _root_.Complex in
private theorem exp_neg_two_arg_mul_I {z : ℂ} (hz : z ≠ 0) :
    exp (((-2 * _root_.Complex.arg z : ℝ) : ℂ) * _root_.Complex.I) = conj z / z := by
  have hn : (‖z‖ : ℂ) ≠ 0 := _root_.Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have he : _root_.Complex.exp ((_root_.Complex.arg z : ℂ) * _root_.Complex.I) = z / ‖z‖ := by
    apply (eq_div_iff hn).mpr
    simpa only [mul_comm] using _root_.Complex.norm_mul_exp_arg_mul_I z
  have hc : conj (_root_.Complex.exp ((_root_.Complex.arg z : ℂ) * _root_.Complex.I)) = _root_.Complex.exp (-((_root_.Complex.arg z : ℂ) * _root_.Complex.I)) := by
    rw [← _root_.Complex.exp_conj]
    congr 1
    simp
  have hp : _root_.Complex.exp (((-2 * _root_.Complex.arg z : ℝ) : ℂ) * _root_.Complex.I) =
      exp (-((_root_.Complex.arg z : ℂ) * _root_.Complex.I)) / _root_.Complex.exp ((_root_.Complex.arg z : ℂ) * _root_.Complex.I) := by
    rw [← _root_.Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [hp, ← hc, he, map_div₀, _root_.Complex.conj_ofReal]
  field_simp

run_cmd do
  let target := ``Submission.Complex.exp_neg_two_arg_mul_I
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `Complex.exp_neg_two_arg_mul_I target :: scope.openDecls } }

open _root_.Complex in
theorem exp_diskBoundaryArgumentLift {a η : ℂ} (ha : ‖a‖ < 1) (hη : ‖η‖ = 1) (t : ℝ) :
    _root_.Complex.exp ((2 * Real.pi * diskBoundaryArgumentLift a η t : ℝ) * _root_.Complex.I) =
      η * ((_root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I) - a) /
        (1 - conj a * _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I))) := by
  let z : ℂ := _root_.Complex.exp ((2 * Real.pi * t : ℝ) * _root_.Complex.I)
  let d : ℂ := 1 - conj a * z
  have hz : ‖z‖ = 1 := _root_.Complex.norm_exp_ofReal_mul_I _
  have hd : d ≠ 0 := by
    intro h
    have hp := diskMoebius_denominator_re_pos ha hz.le
    change 0 < d.re at hp
    simp [h] at hp
  have heta : _root_.Complex.exp ((_root_.Complex.arg η : ℂ) * _root_.Complex.I) = η := by
    simpa [hη] using _root_.Complex.norm_mul_exp_arg_mul_I η
  have hangle : ((2 * Real.pi * diskBoundaryArgumentLift a η t : ℝ) : ℂ) * _root_.Complex.I =
      ((2 * Real.pi * t : ℝ) : ℂ) * _root_.Complex.I + (_root_.Complex.arg η : ℂ) * _root_.Complex.I + ((-2 * _root_.Complex.arg d : ℝ) : ℂ) * I := by
    dsimp [diskBoundaryArgumentLift, d, z]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hangle, _root_.Complex.exp_add, _root_.Complex.exp_add, heta, exp_neg_two_arg_mul_I hd]
  change z * η * (conj d / d) = η * ((z - a) / d)
  have hzz : z * conj z = 1 := by rw [_root_.Complex.mul_conj, _root_.Complex.normSq_eq_norm_sq, hz]; norm_num
  have hzd : z * conj d = z - a := by
    dsimp [d]
    simp only [map_sub, map_one, map_mul, _root_.Complex.conj_conj]
    rw [show z * (1 - a * conj z) = z - a * (z * conj z) by ring, hzz, mul_one]
  rw [← mul_div_assoc, show z * η * conj d = η * (z * conj d) by ring, hzd, mul_div_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Complex.exp_diskBoundaryArgumentLift then
    throwError "Refusing to shadow existing declaration Complex.exp_diskBoundaryArgumentLift"
  Lean.modifyEnv fun env => Lean.addAlias env `Complex.exp_diskBoundaryArgumentLift ``Submission.Complex.exp_diskBoundaryArgumentLift

end Complex

end
