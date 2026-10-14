import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Completion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem finiteHorn_exists_sphere_point_near_endpoint (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (x : W) {rho : ℝ} (hrho : 0 ≤ rho)
    (hr : rho < _root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint) :
    ∃ y : W, _root_.Dist.dist x y = rho ∧
      _root_.Dist.dist (y : UniformSpace.Completion W) H.endpoint <
        2 * (_root_.Dist.dist (x : UniformSpace.Completion W) H.endpoint - rho) := by
  exact Geometry.exists_sphere_point_near_completion_point g
    (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm)
    H.endpoint x hrho hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_sphere_point_near_endpoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_sphere_point_near_endpoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_sphere_point_near_endpoint ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_sphere_point_near_endpoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
