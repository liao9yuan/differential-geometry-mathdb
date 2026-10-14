import Submission.DifferentialGeometry.Geometry.Metric.Cylinder
import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Submission.DifferentialGeometry.Geometry.Metric.Scaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.RealInnerProductSpace
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry

namespace DifferentialGeometry.Geometry.Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

def roundCylinderMetric :
    SmoothRiemannianMetric ((𝓡 n).prod 𝓘(ℝ)) (Metric.sphere (0 : E) 1 × ℝ) :=
  cylinderMetric (scaleMetric 2 (by norm_num) (roundMetric (E := E) (n := n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.roundCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.roundCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.roundCylinderMetric ``Submission.DifferentialGeometry.Geometry.Metric.roundCylinderMetric

@[simp] theorem roundCylinderMetric_inner (x : Metric.sphere (0 : E) 1 × ℝ)
    (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ)) x) :
    (roundCylinderMetric (E := E) (n := n)).inner x v w =
      2 * _root_.Inner.inner ℝ (dIncl x.1 v.1) (dIncl x.1 w.1) + v.2 * w.2 := by
  rw [roundCylinderMetric, cylinderMetric_inner]
  exact congrArg (fun a : ℝ ↦ 2 * a + v.2 * w.2) (roundMetric_inner x.1 v.1 w.1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner ``Submission.DifferentialGeometry.Geometry.Metric.roundCylinderMetric_inner

end DifferentialGeometry.Geometry.Metric
