import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission






noncomputable section

open _root_.Set _root_.InnerProductSpace
open scoped _root_.Topology _root_.ContDiff _root_.ComplexConjugate _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis


def diskImageLogKernel (w z : ℂ) : ℝ := Real.log ‖1 - conj w * z‖

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskImageLogKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskImageLogKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskImageLogKernel ``Submission.DifferentialGeometry.Analysis.diskImageLogKernel


def diskNeumannLogKernel (w z : ℂ) : ℝ := Real.log ‖z - w‖ + diskImageLogKernel w z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskNeumannLogKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskNeumannLogKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskNeumannLogKernel ``Submission.DifferentialGeometry.Analysis.diskNeumannLogKernel



theorem diskImageLogKernel_argument_ne_zero {w z : ℂ} (h : ‖w‖ * ‖z‖ < 1) :
    1 - conj w * z ≠ 0 := by
  intro he
  have hh := congrArg _root_.Norm.norm (sub_eq_zero.mp he)
  simp only [_root_.NormOneClass.norm_one, norm_mul, Complex.norm_conj] at hh
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.diskImageLogKernel_argument_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.diskImageLogKernel_argument_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.diskImageLogKernel_argument_ne_zero ``Submission.DifferentialGeometry.Analysis.diskImageLogKernel_argument_ne_zero


theorem contDiffOn_diskImageLogKernel :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℂ => diskImageLogKernel q.1 q.2)
      {q | ‖q.1‖ * ‖q.2‖ < 1} := by
  have h : ContDiff ℝ ∞ (fun q : ℂ × ℂ => 1 - conj q.1 * q.2) := by
    exact contDiff_const.sub ((Complex.conjCLE.contDiff.comp contDiff_fst).mul contDiff_snd)
  exact (h.contDiffOn.norm ℝ (fun _ hq => diskImageLogKernel_argument_ne_zero hq)).log
    (fun _ hq => norm_ne_zero_iff.mpr (diskImageLogKernel_argument_ne_zero hq))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.contDiffOn_diskImageLogKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.contDiffOn_diskImageLogKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.contDiffOn_diskImageLogKernel ``Submission.DifferentialGeometry.Analysis.contDiffOn_diskImageLogKernel



theorem harmonicAt_diskImageLogKernel {w z : ℂ} (h : ‖w‖ * ‖z‖ < 1) :
    HarmonicAt (diskImageLogKernel w) z := by
  apply AnalyticAt.harmonicAt_log_norm
  · fun_prop
  · exact diskImageLogKernel_argument_ne_zero h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.harmonicAt_diskImageLogKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.harmonicAt_diskImageLogKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.harmonicAt_diskImageLogKernel ``Submission.DifferentialGeometry.Analysis.harmonicAt_diskImageLogKernel



theorem hasDerivAt_log_norm_complex {f : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (h : HasDerivAt f v t) (hne : f t ≠ 0) :
    HasDerivAt (fun r => Real.log ‖f r‖) (_root_.Inner.inner ℝ (f t) v / ‖f t‖ ^ 2) t := by
  have hsq : ‖f t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have hl := (h.norm_sq.log hsq).div_const 2
  have heq : (fun r => Real.log (‖f r‖ ^ 2) / 2) = (fun r => Real.log ‖f r‖) := by
    funext r
    rw [Real.log_pow]
    ring
  rw [heq] at hl
  have hd : 2 * _root_.Inner.inner ℝ (f t) v / ‖f t‖ ^ 2 / 2 = _root_.Inner.inner ℝ (f t) v / ‖f t‖ ^ 2 := by ring
  rw [hd] at hl
  exact hl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.hasDerivAt_log_norm_complex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.hasDerivAt_log_norm_complex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.hasDerivAt_log_norm_complex ``Submission.DifferentialGeometry.Analysis.hasDerivAt_log_norm_complex

end DifferentialGeometry.Analysis
