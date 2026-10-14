import Submission.DifferentialGeometry.Analysis.InnerProductSpace.Laplacian
import Mathlib.Tactic.Linarith

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.InnerProductSpace _root_.Submission.InnerProductSpace

open _root_.ContDiffAt in
theorem ContDiffAt.le_laplacian_norm_sq_of_norm_laplacian_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) {β : ℝ}
    (hΔ : ‖Laplacian.laplacian f x‖ ≤
      β * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x)) :
    2 * (1 - β * ‖f x‖) * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x) ≤
      Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x := by
  have hi := (abs_le.mp (abs_real_inner_le_norm (f x) (Laplacian.laplacian f x))).1
  have hm := mul_le_mul_of_nonneg_left hΔ (norm_nonneg (f x))
  rw [hf.laplacian_norm_sq]
  nlinarith only [hi, hm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffAt.le_laplacian_norm_sq_of_norm_laplacian_le then
    throwError "Refusing to shadow existing declaration ContDiffAt.le_laplacian_norm_sq_of_norm_laplacian_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffAt.le_laplacian_norm_sq_of_norm_laplacian_le ``Submission.ContDiffAt.le_laplacian_norm_sq_of_norm_laplacian_le


open _root_.ContDiffAt in
theorem ContDiffAt.laplacian_norm_sq_nonneg_of_norm_laplacian_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) {β : ℝ}
    (hΔ : ‖Laplacian.laplacian f x‖ ≤
      β * (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x))
    (hsmall : β * ‖f x‖ ≤ 1) :
    0 ≤ Laplacian.laplacian (fun y => ‖f y‖ ^ 2) x := by
  have henergy : 0 ≤ (fderiv ℝ f x).hilbertSchmidtInner (fderiv ℝ f x) := by
    unfold ContinuousLinearMap.hilbertSchmidtInner
    exact Finset.sum_nonneg fun _ _ => real_inner_self_nonneg
  exact (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hsmall)) henergy).trans
    (hf.le_laplacian_norm_sq_of_norm_laplacian_le hΔ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `ContDiffAt.laplacian_norm_sq_nonneg_of_norm_laplacian_le then
    throwError "Refusing to shadow existing declaration ContDiffAt.laplacian_norm_sq_nonneg_of_norm_laplacian_le"
  Lean.modifyEnv fun env => Lean.addAlias env `ContDiffAt.laplacian_norm_sq_nonneg_of_norm_laplacian_le ``Submission.ContDiffAt.laplacian_norm_sq_nonneg_of_norm_laplacian_le
