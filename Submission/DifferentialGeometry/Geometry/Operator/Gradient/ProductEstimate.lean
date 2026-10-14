import Submission.DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem normSq0S_differential1FormFun_mul_le
    (g : SmoothRiemannianMetric I M) {f h : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    normSq0S (I := I) g x 1 (differential1FormFun (I := I) (fun y => f y * h y) x) ≤
      2 * f x ^ 2 * normSq0S (I := I) g x 1 (differential1FormFun (I := I) h x) +
        2 * h x ^ 2 * normSq0S (I := I) g x 1 (differential1FormFun (I := I) f x) := by
  have heq : differential1FormFun (I := I) (fun y => f y * h y) x =
      f x • differential1FormFun (I := I) h x +
        h x • differential1FormFun (I := I) f x := by
    unfold differential1FormFun
    rw [_root_.mvfderiv_fun_mul hf hh]
    change dualToCotangentLinear (I := I)
      (f x • (mvfderiv (I := I) h x).toLinearMap +
        h x • (mvfderiv (I := I) f x).toLinearMap) = _
    rw [map_add, map_smul, map_smul]
    rfl
  rw [heq]
  simpa only [normSq0S_smul, mul_assoc] using
    _root_.Submission.Tensor0SBundle.normSq0S_add_le (I := I) g x 1
      (f x • differential1FormFun (I := I) h x)
      (h x • differential1FormFun (I := I) f x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normSq0S_differential1FormFun_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normSq0S_differential1FormFun_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normSq0S_differential1FormFun_mul_le ``Submission.DifferentialGeometry.Geometry.Operator.normSq0S_differential1FormFun_mul_le

end DifferentialGeometry.Geometry.Operator
