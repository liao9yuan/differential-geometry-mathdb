import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood
import Submission.DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion

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
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_exists_local_complete_metric
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ p : W,
      _root_.Dist.dist (p : UniformSpace.Completion W) H.endpoint < d →
      ∃ (g' : SmoothRiemannianMetric I3 W) (r : ℝ) (U : Set W),
        0 < r ∧ RiemannianMetricComplete g' ∧ IsOpen U ∧
        Metric.closedBall p (4 * r) ⊆ U ∧
        (∀ z ∈ U, g'.inner z = g.inner z) ∧
        (∀ z (v : TangentSpace I3 z), g.inner z v v ≤ g'.inner z v v) ∧
        ∀ x ∈ Metric.ball p r, ∀ y ∈ Metric.ball p r,
          riemannianEDistOf g' x y = ENNReal.ofReal (_root_.Dist.dist x y) := by
  refine ⟨1, zero_lt_one, fun p _ => ?_⟩
  exact Geometry.exists_riemannianMetricComplete_eqOn_ball g
    (fun x y => (edist_dist x y).trans (edist_eq_ofReal_dist g H x y).symm) p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_local_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_local_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_local_complete_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.finiteHorn_exists_local_complete_metric

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
