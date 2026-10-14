import Submission.DifferentialGeometry.Geometry.Metric.Variation.TimeDerivativeBounds
import Mathlib.Analysis.Complex.Exponential

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Analysis

theorem scaled_speed_bound
    (n : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤
      _root_.Min.min (1 / 100 : ℝ) (1 / (16 * (1 + 2 * A + 4 * (n : ℝ) ^ 2) ^ 2)))
    (F F' : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hLscale : L ≤ Real.sqrt epsilon)
    (hF : ∀ q ∈ _root_.Set.Icc (0 : ℝ) L, 0 ≤ F q)
    (hderiv : ∀ q ∈ _root_.Set.Icc (0 : ℝ) L, HasDerivAt F (F' q) q)
    (hbound : ∀ q ∈ _root_.Set.Icc (0 : ℝ) L,
      |F' q| ≤ 4 * A * q ^ 2 * Real.sqrt (F q) + 4 * (n : ℝ) ^ 2 * q * F q)
    (hinit : F 0 ≤ 1 / (25 * epsilon)) :
    ∀ q ∈ _root_.Set.Icc (0 : ℝ) L, F q ≤ 1 / (15 * epsilon) := by
  let C : ℝ := 1 + 2 * A + 4 * (n : ℝ) ^ 2
  have hC : 0 < C := by dsimp only [C]; positivity
  have heps100 : epsilon ≤ 1 / 100 := hepsilonSmall.trans (min_le_left _ _)
  have hepsC : epsilon ≤ 1 / (16 * C ^ 2) := hepsilonSmall.trans (min_le_right _ _)
  have hroot : Real.sqrt epsilon ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by nlinarith only [heps100]⟩
  have hCsq : (C * Real.sqrt epsilon) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 16 * C ^ 2)).mp hepsC
    rw [mul_pow, Real.sq_sqrt hepsilon.le]
    nlinarith only [hmul]
  have hCroot : C * Real.sqrt epsilon ≤ 1 / 4 :=
    (sq_le_sq₀ (mul_nonneg hC.le (Real.sqrt_nonneg epsilon)) (by norm_num)).mp hCsq
  have hlinear (q : ℝ) (hq : q ∈ _root_.Set.Icc (0 : ℝ) L) : |F' q| ≤ C * F q + C := by
    have hq1 : q ≤ 1 := hq.2.trans (hLscale.trans hroot)
    have hq2 : q ^ 2 ≤ 1 := by nlinarith only [hq.1, hq1]
    have hFq := hF q hq
    have hsqrt : 2 * Real.sqrt (F q) ≤ F q + 1 := by
      have hsquare := Real.sq_sqrt hFq
      nlinarith only [hsquare, sq_nonneg (Real.sqrt (F q) - 1)]
    have hgradScale := mul_le_mul_of_nonneg_right hq2
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hA) (Real.sqrt_nonneg (F q)))
    have hricScale := mul_le_mul_of_nonneg_right hq1
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg (n : ℝ))) hFq)
    have hYoung := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
    have hraw := hbound q hq
    dsimp only [C]
    nlinarith only [hraw, hgradScale, hricScale, hYoung, hFq, hA, sq_nonneg (n : ℝ)]
  intro q hq
  have hsub : _root_.Set.uIcc (0 : ℝ) q ⊆ _root_.Set.Icc (0 : ℝ) L := by
    rw [_root_.Set.uIcc_of_le hq.1]
    exact _root_.Set.Icc_subset_Icc le_rfl hq.2
  have hgron := affineGronwall_of_abs_deriv_le F F' (t0 := 0) (t := q)
    (alpha := C) (beta := C) hC hC
    (fun s hs ↦ hF s (hsub hs)) (fun s hs ↦ hderiv s (hsub hs))
    (fun s hs ↦ hlinear s (hsub hs))
  rw [sub_zero, abs_of_nonneg hq.1, div_self hC.ne'] at hgron
  have hCq : C * q ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (hq.2.trans hLscale) hC.le).trans hCroot
  have hexp : Real.exp (C * q) ≤ 4 / 3 := by
    have hnonneg := mul_nonneg hC.le hq.1
    have hlt : C * q < 1 := by linarith only [hCq]
    apply (Real.exp_bound_div_one_sub_of_interval hnonneg hlt).trans
    apply (div_le_iff₀ (sub_pos.mpr hlt)).mpr
    nlinarith only [hCq]
  have hF0 : 0 ≤ F 0 := hF 0 ⟨le_rfl, hL⟩
  have hupper : F q ≤ (4 / 3 : ℝ) * (F 0 + 1) :=
    hgron.trans (mul_le_mul_of_nonneg_right hexp (by linarith only [hF0]))
  have hbudget : (4 / 3 : ℝ) * (F 0 + 1) ≤ 1 / (15 * epsilon) := by
    have hinitMul := (le_div_iff₀ (by positivity : 0 < 25 * epsilon)).mp hinit
    apply (le_div_iff₀ (by positivity : 0 < 15 * epsilon)).mpr
    nlinarith only [hinitMul, heps100]
  exact hupper.trans hbudget

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.scaled_speed_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.scaled_speed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.scaled_speed_bound ``Submission.DifferentialGeometry.Analysis.scaled_speed_bound

end DifferentialGeometry.Analysis

end
