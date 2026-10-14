import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalIterCov

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instIsManifoldRealOfNatWithTopENat_differentialGeometry_1 target :: scope.openDecls } }

theorem normSq0S_metricRm04At_localPullMetric
    (g : SmoothRiemannianMetric I N) (f : M → N) (hf : IsLocalDiffeomorph I I ∞ f) (x : M) :
    normSq0S (localPullMetric g f hf) x 4 (metricRm04At (localPullMetric g f hf) x) =
      normSq0S g (f x) 4 (metricRm04At g (f x)) := by
  exact Geometry.Tensor.normSq0S_iterCov_localPullMetric g f hf
    (metricRm04 (localPullMetric g f hf)) (metricRm04 g)
    (fun y v => metricRm04StandardAt_localPullMetric g f hf y (v 0) (v 1) (v 2) (v 3)) 0 x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.normSq0S_metricRm04At_localPullMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.normSq0S_metricRm04At_localPullMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.normSq0S_metricRm04At_localPullMetric ``Submission.DifferentialGeometry.Geometry.Curvature.normSq0S_metricRm04At_localPullMetric

end DifferentialGeometry.Geometry.Curvature
