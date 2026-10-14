import Submission.DifferentialGeometry.Geometry.Curvature.Product
import Submission.DifferentialGeometry.Geometry.Curvature.Line
import Submission.DifferentialGeometry.Geometry.Metric.Cylinder

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Curvature

theorem ricciTensor_cylinderMetric
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M × ℝ)
    (v w : TangentSpace (I.prod 𝓘(ℝ)) x) :
    ricciTensor (cylinderMetric g) x v w = ricciTensor g x.1 v.1 w.1 := by
  unfold cylinderMetric
  refine (ricciTensor_productMetric g _ x v w).trans ?_
  exact (congrArg (fun a : ℝ ↦ ricciTensor g x.1 v.1 w.1 + a)
    (ricciTensor_line_eq_zero _ x.2 v.2 w.2)).trans (add_zero _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.ricciTensor_cylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.ricciTensor_cylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.ricciTensor_cylinderMetric ``Submission.DifferentialGeometry.Geometry.Curvature.ricciTensor_cylinderMetric

end DifferentialGeometry.Geometry.Curvature
