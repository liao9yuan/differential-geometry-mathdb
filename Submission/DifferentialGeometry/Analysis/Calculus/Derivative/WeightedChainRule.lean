import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Filter
open scoped _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weighted_second_deriv_comp {a : ℝ → ℝ} {f : ℝ → F} {φ : F → ℝ} {x : ℝ}
    (ha : DifferentiableAt ℝ a x) (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    a x * deriv (fun y => a y * deriv (fun z => φ (f z)) y) x =
      fderiv ℝ (fderiv ℝ φ) (f x) (a x • deriv f x) (a x • deriv f x) +
        fderiv ℝ φ (f x) (a x • deriv (fun y => a y • deriv f y) x) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hnear : (fun y => a y * deriv (fun z => φ (f z)) y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ φ (f y) (a y • deriv f y)) := by
    filter_upwards [hf.eventually (by norm_num),
      hfd.continuousAt (hφ.eventually (by norm_num))] with y hy hφy
    change ContDiffAt ℝ 2 φ (f y) at hφy
    have hd := ((hφy.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt y
      (hy.differentiableAt (by norm_num)).hasDerivAt).deriv
    dsimp only [Function.comp_def] at hd
    rw [hd, map_smul, smul_eq_mul]
  have hφd : DifferentiableAt ℝ (fderiv ℝ φ) (f x) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfg : DifferentiableAt ℝ (fun y => a y • deriv f y) x :=
    ha.smul ((hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hd := ((hφd.hasFDerivAt.comp_hasDerivAt x hfd.hasDerivAt).clm_apply hfg.hasDerivAt).deriv
  dsimp only [Function.comp_def] at hd
  rw [hnear.deriv_eq, hd]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.weighted_second_deriv_comp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.weighted_second_deriv_comp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.weighted_second_deriv_comp ``Submission.DifferentialGeometry.Analysis.weighted_second_deriv_comp


theorem norm_weighted_second_deriv_comp_le {a : ℝ → ℝ} {f : ℝ → F} {φ : F → ℝ} {x : ℝ}
    (ha : DifferentiableAt ℝ a x) (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    ‖a x * deriv (fun y => a y * deriv (fun z => φ (f z)) y) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ φ) (f x)‖ * ‖a x • deriv f x‖ ^ 2 +
        ‖fderiv ℝ φ (f x)‖ * ‖a x • deriv (fun y => a y • deriv f y) x‖ := by
  rw [weighted_second_deriv_comp ha hf hφ]
  refine (norm_add_le _ _).trans (add_le_add ?_ (ContinuousLinearMap.le_opNorm _ _))
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have h := mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm
    (fderiv ℝ (fderiv ℝ φ) (f x)) (a x • deriv f x)) (norm_nonneg (a x • deriv f x))
  simpa only [pow_two, mul_assoc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_weighted_second_deriv_comp_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_weighted_second_deriv_comp_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_weighted_second_deriv_comp_le ``Submission.DifferentialGeometry.Analysis.norm_weighted_second_deriv_comp_le

end DifferentialGeometry.Analysis
