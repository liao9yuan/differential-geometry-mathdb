import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.Geometry.Gradient

theorem abs_mvfderiv_signed_difference_le_gradient_norm
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (u v : M → ℝ) (σ : ℝ)
    (x : M) (z : TangentSpace I x) :
    |mvfderiv I u x z - σ * mvfderiv I v x z| ≤
      Real.sqrt (g.inner x (gradFun g u x - σ • gradFun g v x)
        (gradFun g u x - σ • gradFun g v x)) * Real.sqrt (g.inner x z z) := by
  have h := abs_metric_inner_le_sqrt_metric_quadratic g x
    (gradFun g u x - σ • gradFun g v x) z
  have he : g.inner x (gradFun g u x - σ • gradFun g v x) z =
      mvfderiv I u x z - σ * mvfderiv I v x z := by
    rw [map_sub, sub_apply, map_smul, smul_apply, inner_gradFun, inner_gradFun]
    rfl
  rwa [he] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Gradient.abs_mvfderiv_signed_difference_le_gradient_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Gradient.abs_mvfderiv_signed_difference_le_gradient_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Gradient.abs_mvfderiv_signed_difference_le_gradient_norm ``Submission.DifferentialGeometry.Geometry.Gradient.abs_mvfderiv_signed_difference_le_gradient_norm

end DifferentialGeometry.Geometry.Gradient
