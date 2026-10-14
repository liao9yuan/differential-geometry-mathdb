import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskMetricDerivative
import Submission.DifferentialGeometry.Geometry.Connection.SourceCovariantPartial

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission






noncomputable section

open _root_.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry _root_.Filter
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ContDiff _root_.Bundle _root_.Submission.Bundle _root_.Manifold

namespace DifferentialGeometry.Geometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.AlongCurve
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem diskMapCovariantPartial_chart
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    let F := (extChartAt 𝓘(ℝ, E) (U z)) ∘ U
    (_root_.FiberBundle.trivializationAt E (TangentSpace 𝓘(ℝ, E)) (U z)).continuousLinearMapAt ℝ (U z)
        (diskMapCovariantPartial g U z v w) =
      fderiv ℝ (fun q => fderiv ℝ F q w) z v +
        chartChristoffelContraction g (U z) (fderiv ℝ F z v) (fderiv ℝ F z w) (F z) :=
  sourceCovariantPartial_chart g hs hU hz v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantPartial_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantPartial_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantPartial_chart ``Submission.DifferentialGeometry.Geometry.diskMapCovariantPartial_chart



theorem diskMapCovariantPartial_symm
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    diskMapCovariantPartial g U z v w = diskMapCovariantPartial g U z w v :=
  sourceCovariantPartial_symm g hs hU hz v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapCovariantPartial_symm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapCovariantPartial_symm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapCovariantPartial_symm ``Submission.DifferentialGeometry.Geometry.diskMapCovariantPartial_symm

end DifferentialGeometry.Geometry
