import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Connected
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Function
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }
universe u

structure SmoothSelfAttachment {M : ConnectedClosedOrientedManifold.{u} 3}
    (c d : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
    (a : BoundaryAttachment) where
  [charts : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph)]
  [smooth : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph)]
  orientation : ManifoldOrientation (𝓡 3) (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) 3
  core_localDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
  band_localDiffeomorph : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
  lower_localDiffeomorph : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph) (SelfAttachment.collarZero z)
  upper_localDiffeomorph : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph) (SelfAttachment.collarZero z)
  core_preserves_orientation : ∀ x, Orientation.map (Fin 3)
    (core_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (M.orientation.orientation x.val) = orientation.orientation
        (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothSelfAttachment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothSelfAttachment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothSelfAttachment ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment

namespace SmoothSelfAttachment

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment}

def toConnectedClosedOrientedManifold (s : SmoothSelfAttachment c d hcd a) : ConnectedClosedOrientedManifold.{u} 3 where
  Carrier := SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph
  topology := inferInstance
  charts := s.charts
  smooth := s.smooth
  hausdorff := inferInstance
  compact := inferInstance
  connected := SelfAttachment.connectedSpace_quotient c d hcd a.val.toHomeomorph
  orientation := s.orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothSelfAttachment.toConnectedClosedOrientedManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothSelfAttachment.toConnectedClosedOrientedManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothSelfAttachment.toConnectedClosedOrientedManifold ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment.toConnectedClosedOrientedManifold

end SmoothSelfAttachment
end DifferentialGeometry.Topology
