import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import Submission.DifferentialGeometry.Topology.Connected.FiniteEDistance

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry
open scoped _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianMetricComplete_of_compact [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) : RiemannianMetricComplete g := by
  unfold RiemannianMetricComplete
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianMetricComplete_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianMetricComplete_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianMetricComplete_of_compact ``Submission.DifferentialGeometry.Geometry.riemannianMetricComplete_of_compact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDistOf_ne_top_of_preconnected [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x y : M) : riemannianEDistOf g x y ≠ ⊤ := by
  let cg := g.toContinuousRiemannianMetric
  let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨cg.toRiemannianMetric⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  exact DifferentialGeometry.Analysis.edist_ne_top_of_preconnected x y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.riemannianEDistOf_ne_top_of_preconnected then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.riemannianEDistOf_ne_top_of_preconnected"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.riemannianEDistOf_ne_top_of_preconnected ``Submission.DifferentialGeometry.Geometry.riemannianEDistOf_ne_top_of_preconnected

end DifferentialGeometry.Geometry
