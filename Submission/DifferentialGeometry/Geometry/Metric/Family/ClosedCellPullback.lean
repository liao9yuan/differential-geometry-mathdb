import Submission.DifferentialGeometry.Topology.Manifold.ClosedCellChart
import Submission.DifferentialGeometry.Geometry.Metric.Family.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Connection

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell target :: scope.openDecls } }

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
  (Φ : PartialDiffeomorph (𝓡 (m + 1)) I
    (EuclideanSpace ℝ (Fin (m + 1))) M ∞)
  (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 < r)
  (hsource : Metric.closedBall c r ⊆ Φ.source)

def closedCellPullbackMetricFamily :
    MetricConnectionFamilyOn (I := 𝓡∂ (m + 1)) (M := ClosedCell (m + 1)) D where
  metric t := (g t).pullback (closedCellChartMap Φ c r)
    (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (injective_mfderiv_closedCellChartMap Φ c hr hsource)
  connection t := leviCivitaConnectionOfMetric
    ((g t).pullback (closedCellChartMap Φ c r)
      (contMDiff_closedCellChartMap Φ c hr.le hsource)
      (injective_mfderiv_closedCellChartMap Φ c hr hsource))
  metricCompatible _ := leviCivitaConnectionOfMetric_isMetricCompatible _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily ``Submission.DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily

omit [FiniteDimensional ℝ E] in
@[simp]
theorem closedCellPullbackMetricFamily_inner (t : ℝ) (x : ClosedCell (m + 1))
    (v w : TangentSpace (𝓡∂ (m + 1)) x) :
    ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric t).inner x v w =
      (g t).inner (Φ (c + r • x.val))
        (mfderiv (𝓡∂ (m + 1)) I (closedCellChartMap Φ c r) x v)
        (mfderiv (𝓡∂ (m + 1)) I (closedCellChartMap Φ c r) x w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily_inner ``Submission.DifferentialGeometry.Geometry.Curvature.closedCellPullbackMetricFamily_inner

theorem metricFamilySmoothOn_closedCellPullbackMetricFamily
    (hg : MetricFamilySmoothOn D g) :
    MetricFamilySmoothOn D (closedCellPullbackMetricFamily D g Φ c hr hsource).metric :=
  hg.of_pullback (closedCellPullbackMetricFamily D g Φ c hr hsource).metric
    (closedCellChartMap Φ c r) (contMDiff_closedCellChartMap Φ c hr.le hsource)
    (fun _ _ _ _ => rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_closedCellPullbackMetricFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_closedCellPullbackMetricFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_closedCellPullbackMetricFamily ``Submission.DifferentialGeometry.Geometry.Curvature.metricFamilySmoothOn_closedCellPullbackMetricFamily

end DifferentialGeometry.Geometry.Curvature
