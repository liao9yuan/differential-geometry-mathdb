import Submission.DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Riemannian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace Tensor
namespace RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable def tangentContinuousRiemannianMetric
    (g : DifferentialGeometry.SmoothRiemannianMetric I M) :
    Bundle.ContinuousRiemannianMetric E (TangentSpace I : M → Type _) :=
  g.toContinuousRiemannianMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric ``Submission.DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric

omit [FiniteDimensional ℝ E] in
@[simp] theorem tangentContinuousRiemannianMetric_inner
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    (b : M) :
    (tangentContinuousRiemannianMetric (I := I) (M := M) g).inner b = g.inner b :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric_inner ``Submission.DifferentialGeometry.Tensor.RSTensor.tangentContinuousRiemannianMetric_inner

end RSTensor
end Tensor
end DifferentialGeometry

end
