import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

namespace QuadraticForm
open _root_.QuadraticForm

open _root_.QuadraticForm in
theorem equivalent_sq_smul {R E : Type*} [CommSemiring R] [AddCommMonoid E] [Module R E]
    (Q : QuadraticForm R E) {c : R} (hc : IsUnit c) :
    QuadraticMap.Equivalent (c ^ 2 • Q) Q := by
  refine ⟨{ LinearEquiv.smulOfUnit hc.unit with map_app' := ?_ }⟩
  intro x
  change Q ((hc.unit : R) • x) = c ^ 2 * Q x
  rw [hc.unit_spec, Q.map_smul]
  simp only [smul_eq_mul, pow_two]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `QuadraticForm.equivalent_sq_smul then
    throwError "Refusing to shadow existing declaration QuadraticForm.equivalent_sq_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `QuadraticForm.equivalent_sq_smul ``Submission.QuadraticForm.equivalent_sq_smul

open _root_.QuadraticForm in
theorem equivalent_smul_of_pos {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (Q : QuadraticForm ℝ E) {c : ℝ} (hc : 0 < c) :
    QuadraticMap.Equivalent (c • Q) Q := by
  simpa only [Real.sq_sqrt hc.le] using
    Q.equivalent_sq_smul (isUnit_iff_ne_zero.2 (ne_of_gt (Real.sqrt_pos.2 hc)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `QuadraticForm.equivalent_smul_of_pos then
    throwError "Refusing to shadow existing declaration QuadraticForm.equivalent_smul_of_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `QuadraticForm.equivalent_smul_of_pos ``Submission.QuadraticForm.equivalent_smul_of_pos

end QuadraticForm
