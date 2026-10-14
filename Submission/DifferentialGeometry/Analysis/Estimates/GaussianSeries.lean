import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis


theorem summable_exp_neg_mul_sq (c : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ ↦ Real.exp (-c * (k : ℝ) ^ 2)) := by
  exact Real.summable_exp_nat_mul_of_ge (c := -c) (neg_lt_zero.mpr hc)
    (f := fun k : ℕ ↦ (k : ℝ) ^ 2) fun k ↦ by
      exact_mod_cast Nat.le_pow (a := k) (b := 2) (by omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.summable_exp_neg_mul_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.summable_exp_neg_mul_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.summable_exp_neg_mul_sq ``Submission.DifferentialGeometry.Analysis.summable_exp_neg_mul_sq


theorem summable_exp_neg_mul_sq_add_mul (c C : ℝ) (hc : 0 < c) :
    Summable (fun k : ℕ ↦ Real.exp (-c * (k : ℝ) ^ 2 + C * (k : ℝ))) := by
  have hbound (x : ℝ) :
      -c * x ^ 2 + C * x ≤ -(c / 2) * x ^ 2 + C ^ 2 / (2 * c) := by
    have haux : -c * x ^ 2 + C * x + (c / 2) * x ^ 2 ≤ C ^ 2 / (2 * c) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * c)).2
      nlinarith [sq_nonneg (c * x - C)]
    linarith
  have hgauss := summable_exp_neg_mul_sq (c / 2) (half_pos hc)
  have hmajor : Summable (fun k : ℕ ↦
      Real.exp (C ^ 2 / (2 * c)) * Real.exp (-(c / 2) * (k : ℝ) ^ 2)) :=
    hgauss.mul_left (Real.exp (C ^ 2 / (2 * c)))
  refine Summable.of_nonneg_of_le (fun k ↦ (Real.exp_pos _).le) ?_ hmajor
  intro k
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [add_comm] using hbound k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.summable_exp_neg_mul_sq_add_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.summable_exp_neg_mul_sq_add_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.summable_exp_neg_mul_sq_add_mul ``Submission.DifferentialGeometry.Analysis.summable_exp_neg_mul_sq_add_mul

theorem tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top (c C : ℝ) (hc : 0 < c) :
    (∑' k : ℕ, ENNReal.ofReal
      (Real.exp (-c * (k : ℝ) ^ 2 + C * (k : ℝ)))) < ⊤ :=
  (summable_exp_neg_mul_sq_add_mul c C hc).tsum_ofReal_lt_top

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top ``Submission.DifferentialGeometry.Analysis.tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top

end DifferentialGeometry.Analysis
