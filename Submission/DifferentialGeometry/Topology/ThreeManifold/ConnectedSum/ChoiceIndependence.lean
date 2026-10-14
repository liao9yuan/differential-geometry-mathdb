import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedFactorBallChart

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u v

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d' a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart c c' d a
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart c' d d' a
  exact ⟨f.trans g⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts

end DifferentialGeometry.Topology
