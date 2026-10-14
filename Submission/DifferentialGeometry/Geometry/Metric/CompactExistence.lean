import Submission.DifferentialGeometry.Geometry.Metric.Construction.Existence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem nonempty_smoothRiemannianMetric_of_compact [CompactSpace M] [T2Space M] :
    Nonempty (Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :=
  DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric_of_compact ``Submission.DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric_of_compact

end DifferentialGeometry.Geometry
