import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L1Space.Integrable

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

open _root_.MeasureTheory
open scoped _root_.BigOperators _root_.ENNReal

namespace MeasureTheory
open _root_.MeasureTheory

variable {α ι F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ : Measure α}

open _root_.MeasureTheory in
theorem integrable_finset_sum_norm_sq
    (s : Finset ι) {v : ι → α → F} (hv : ∀ j ∈ s, _root_.MeasureTheory.MemLp (v j) 2 μ) (C : ℝ) :
    Integrable (fun x => C * ∑ j ∈ s, ‖v j x‖ ^ 2) μ := by
  refine (_root_.MeasureTheory.integrable_finsetSum s fun j hj => ?_).const_mul C
  exact (hv j hj).integrable_norm_pow (by decide)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_finset_sum_norm_sq then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_finset_sum_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_finset_sum_norm_sq ``Submission.MeasureTheory.integrable_finset_sum_norm_sq

open _root_.MeasureTheory in
theorem integrable_finset_sum_quadratic_bound
    (s : Finset ι) {v w : ι → α → F}
    (hv : ∀ j ∈ s, _root_.MeasureTheory.MemLp (v j) 2 μ) (hw : ∀ j ∈ s, _root_.MeasureTheory.MemLp (w j) 2 μ)
    (C P : ℝ) :
    _root_.MeasureTheory.Integrable (fun x => C * ∑ j ∈ s,
      (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖))) μ := by
  refine (_root_.MeasureTheory.integrable_finsetSum s fun j hj => ?_).const_mul C
  have hsum : _root_.MeasureTheory.MemLp (fun x => ‖v j x‖ + ‖w j x‖) 2 μ :=
    (hv j hj).norm.add (hw j hj).norm
  have hsq : _root_.MeasureTheory.Integrable (fun x => (‖v j x‖ + ‖w j x‖) ^ 2) μ := by
    have hmul' := hsum.integrable_mul hsum
    convert hmul' using 1
    ext x
    simp only [Pi.mul_apply, pow_two]
  have hmul : _root_.MeasureTheory.Integrable (fun x => ‖w j x‖ * (‖v j x‖ + ‖w j x‖)) μ :=
    (hw j hj).norm.integrable_mul hsum
  have hadd := (hsq.const_mul P).add (hmul.const_mul 2)
  convert hadd using 1
  ext x
  simp only [Pi.add_apply, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_finset_sum_quadratic_bound then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_finset_sum_quadratic_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_finset_sum_quadratic_bound ``Submission.MeasureTheory.integrable_finset_sum_quadratic_bound

open _root_.MeasureTheory in
theorem integrable_sum_norm_sq
    [Fintype ι] {v : ι → α → F} (hv : ∀ j, _root_.MeasureTheory.MemLp (v j) 2 μ) (C : ℝ) :
    Integrable (fun x => C * ∑ j, ‖v j x‖ ^ 2) μ :=
  integrable_finset_sum_norm_sq Finset.univ (fun j _ => hv j) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_sum_norm_sq then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_sum_norm_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_sum_norm_sq ``Submission.MeasureTheory.integrable_sum_norm_sq

open _root_.MeasureTheory in
theorem integrable_sum_quadratic_bound
    [Fintype ι] {v w : ι → α → F}
    (hv : ∀ j, _root_.MeasureTheory.MemLp (v j) 2 μ) (hw : ∀ j, _root_.MeasureTheory.MemLp (w j) 2 μ) (C P : ℝ) :
    _root_.MeasureTheory.Integrable (fun x => C * ∑ j,
      (P * (‖v j x‖ + ‖w j x‖) ^ 2 + 2 * ‖w j x‖ * (‖v j x‖ + ‖w j x‖))) μ :=
  integrable_finset_sum_quadratic_bound Finset.univ (fun j _ => hv j) (fun j _ => hw j) C P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `MeasureTheory.integrable_sum_quadratic_bound then
    throwError "Refusing to shadow existing declaration MeasureTheory.integrable_sum_quadratic_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `MeasureTheory.integrable_sum_quadratic_bound ``Submission.MeasureTheory.integrable_sum_quadratic_bound

end MeasureTheory

end
