import Submission.DifferentialGeometry.Geometry.Metric.Basic
import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.Riemannian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Set
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def RiemannianMetricComplete [T3Space M] (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : Prop :=
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  CompleteSpace M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.RiemannianMetricComplete then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.RiemannianMetricComplete"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.RiemannianMetricComplete ``Submission.DifferentialGeometry.Geometry.RiemannianMetricComplete

end DifferentialGeometry.Geometry

end

end
