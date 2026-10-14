import Submission.DifferentialGeometry.Geometry.Connection.Trivial
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.CovariantDerivative in
theorem trivial_isMetricCompatible : (trivial I M F).IsMetricCompatible := by
  unfold _root_.CovariantDerivative.IsMetricCompatible
  funext x
  ext v w X
  rw [_root_.CovariantDerivative.derivMetricTensor_apply_eq_extend]
  have hext (a : F) : FiberBundle.extend (E := Bundle.Trivial M F) F (x := x) a = fun _ => a := by
    funext y
    simp [FiberBundle.extend]
  simp only [trivial_apply, hext, mvfderiv_const, Pi.zero_apply, zero_apply,
    inner_zero_left, inner_zero_right, sub_zero]
  change mvfderiv I (fun _ : M => _root_.Inner.inner ℝ v w) x X = 0
  rw [mvfderiv_const, zero_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.trivial_isMetricCompatible then
    throwError "Refusing to shadow existing declaration CovariantDerivative.trivial_isMetricCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.trivial_isMetricCompatible ``Submission.CovariantDerivative.trivial_isMetricCompatible

end CovariantDerivative
