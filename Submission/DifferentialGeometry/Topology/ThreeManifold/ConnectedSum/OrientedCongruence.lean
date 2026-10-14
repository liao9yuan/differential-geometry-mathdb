import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import Submission.DifferentialGeometry.Topology.Manifold.OrientedBallChartMap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u v u' v'

theorem nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    {M' : ConnectedClosedOrientedManifold.{u'} 3} {N' : ConnectedClosedOrientedManifold.{v'} 3}
    (F : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        M'.toClosedOrientedManifold)
    (G : ClosedOrientedManifold.OrientedDiffeomorph N.toClosedOrientedManifold
        N'.toClosedOrientedManifold) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M N).toClosedOrientedManifold (connectedSum M'
          N').toClosedOrientedManifold) := by
  let c := orientedBallChart M
  let d := orientedBallChart N
  obtain ⟨H⟩ := csTransport_diffeomorph_preservesOrientation c (c.map F) d (d.map G)
    boundaryAttachment F.val G.val (fun _ _ => rfl) (fun _ _ => rfl) F.property
  obtain ⟨K⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    (c.map F) (orientedBallChart M') (d.map G) (orientedBallChart N') boundaryAttachment
  exact ⟨H.trans K⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph

end DifferentialGeometry.Topology
