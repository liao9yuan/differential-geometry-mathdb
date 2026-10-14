import Submission.DifferentialGeometry.Geometry.Metric.Conformal.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.NormSquared

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Operator

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem gradientFun_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (f : M → Real) (x : M) :
    gradientFun (conformalMetric g u) f x =
      Real.exp (-(2 * u x)) • gradientFun g f x := by
  apply metricFlatLinear_injective (conformalMetric g u) x
  ext v
  rw [metricFlatLinear_apply, metricFlatLinear_apply, inner_gradientFun,
    conformalMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [inner_gradientFun, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.gradientFun_conformalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.gradientFun_conformalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.gradientFun_conformalMetric ``Submission.DifferentialGeometry.Geometry.Operator.gradientFun_conformalMetric

theorem inner_gradientFun_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (f h : M → Real) (x : M) :
    (conformalMetric g u).inner x
        (gradientFun (conformalMetric g u) f x)
        (gradientFun (conformalMetric g u) h x) =
      Real.exp (-(2 * u x)) * g.inner x (gradientFun g f x) (gradientFun g h x) := by
  rw [gradientFun_conformalMetric, gradientFun_conformalMetric, conformalMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  calc
    _ = (Real.exp (2 * u x) * Real.exp (-(2 * u x))) *
        (Real.exp (-(2 * u x)) * g.inner x (gradientFun g f x) (gradientFun g h x)) := by ring
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.inner_gradientFun_conformalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.inner_gradientFun_conformalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.inner_gradientFun_conformalMetric ``Submission.DifferentialGeometry.Geometry.Operator.inner_gradientFun_conformalMetric

theorem normGradSqFun_conformalMetric
    (g : SmoothRiemannianMetric I M) (u : C^∞⟮I, M; Real⟯)
    (f : M → Real) (x : M) :
    normGradSqFun (conformalMetric g u) f x =
      Real.exp (-(2 * u x)) * normGradSqFun g f x := by
  exact inner_gradientFun_conformalMetric g u f f x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.normGradSqFun_conformalMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.normGradSqFun_conformalMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.normGradSqFun_conformalMetric ``Submission.DifferentialGeometry.Geometry.Operator.normGradSqFun_conformalMetric

end DifferentialGeometry.Geometry.Operator
