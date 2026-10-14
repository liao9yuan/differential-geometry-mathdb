import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Set _root_.MeasureTheory
open scoped _root_.ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le
    {f : E → F} {q y : E} {M : ℝ}
    (hf : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (q + t • (y - q)))
    (hM : ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ 2 f (q + t • (y - q))‖ ≤ M) :
    ‖f y - f q - fderiv ℝ f q (y - q)‖ ≤ M / 2 * ‖y - q‖ ^ 2 := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := q) (y := y - q) (n := 1) hf
  have he : f y = f q + fderiv ℝ f q (y - q) +
      ∫ t in (0 : ℝ)..1, (1 - t) •
        iteratedFDeriv ℝ 2 f (q + t • (y - q)) (fun _ => y - q) := by
    simpa [Finset.sum_range_succ, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply] using ht
  have hremainder : f y - f q - fderiv ℝ f q (y - q) =
      ∫ t in (0 : ℝ)..1, (1 - t) •
        iteratedFDeriv ℝ 2 f (q + t • (y - q)) (fun _ => y - q) := by
    rw [he]
    abel
  rw [hremainder]
  have hweight : IntervalIntegrable (fun t : ℝ => 1 - t) _root_.MeasureTheory.MeasureSpace.volume 0 1 :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - t) * (M * ‖y - q‖ ^ 2) := by
      apply intervalIntegral.norm_integral_le_of_norm_le zero_le_one _
        (hweight.mul_const _)
      exact Filter.Eventually.of_forall fun t ht => by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht.2)
        simpa using ContinuousMultilinearMap.le_of_opNorm_le
          (hM t ⟨ht.1.le, ht.2⟩) (fun _ => y - q)
    _ = M / 2 * ‖y - q‖ ^ 2 := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable _ _)]
      norm_num [integral_id]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le ``Submission.DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le

theorem norm_sub_sub_fderiv_le_of_contDiffOn
    {f : E → F} {U : Set E} {q y : E} {M : ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    (hM : ∀ x ∈ U, ‖iteratedFDeriv ℝ 2 f x‖ ≤ M) (hq : q ∈ U) (hy : y ∈ U) :
    ‖f y - f q - fderiv ℝ f q (y - q)‖ ≤ M / 2 * ‖y - q‖ ^ 2 := by
  apply norm_sub_sub_fderiv_le_of_iteratedFDeriv_two_le
  · intro t ht
    exact hf.contDiffAt (hU.mem_nhds (hconv.add_smul_sub_mem hq hy ht))
  · intro t ht
    exact hM _ (hconv.add_smul_sub_mem hq hy ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.norm_sub_sub_fderiv_le_of_contDiffOn

end DifferentialGeometry.Analysis

end

end
