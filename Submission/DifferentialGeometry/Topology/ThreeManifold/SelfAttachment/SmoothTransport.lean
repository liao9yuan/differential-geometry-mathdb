import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth
import Submission.DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CoreOrientationTransport
import Submission.DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback

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

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.E3 target :: scope.openDecls } }

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (c d : OrientedBallChart M.toClosedOrientedManifold) (c' d' : OrientedBallChart N.toClosedOrientedManifold)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (a : BoundaryAttachment) (F : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold N.toClosedOrientedManifold)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, F.val (c.chart x) = c'.chart x)
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, F.val (d.chart x) = d'.chart x)
  (s : SmoothSelfAttachment c' d' hcd' a)

def SmoothSelfAttachment.pullback : SmoothSelfAttachment c d hcd a := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' a.val.toHomeomorph) := s.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' a.val.toHomeomorph) := s.smooth
  let H := SelfAttachment.homeomorphOfChartTransport c.toBallChart d.toBallChart c'.toBallChart d'.toBallChart
    hcd hcd' F.val.toHomeomorph hc hd a.val.toHomeomorph
  let Q := s.toConnectedClosedOrientedManifold.pullback H
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := Q.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := Q.smooth
  let hlocal := SelfAttachment.local_maps_of_chart_transport c.toBallChart d.toBallChart
    c'.toBallChart d'.toBallChart F.val hc hd hcd hcd' a.val.toHomeomorph
    s.core_localDiffeomorph s.band_localDiffeomorph s.lower_localDiffeomorph s.upper_localDiffeomorph
  let hcore := hlocal.1
  let hband := hlocal.2.1
  let hlower := hlocal.2.2.1
  let hupper := hlocal.2.2.2
  refine {
    charts := Q.charts
    smooth := Q.smooth
    orientation := Q.orientation
    core_localDiffeomorph := hcore
    band_localDiffeomorph := hband
    lower_localDiffeomorph := hlower
    upper_localDiffeomorph := hupper
    core_preserves_orientation := ?_ }
  exact SelfAttachment.core_orientation_of_chart_transport c.toBallChart d.toBallChart c'.toBallChart d'.toBallChart
    F.val hc hd hcd hcd' a.val.toHomeomorph M.orientation N.orientation F.property s.orientation
    s.core_localDiffeomorph s.core_preserves_orientation Q.orientation
    (s.toConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph H).property hcore

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothSelfAttachment.pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothSelfAttachment.pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothSelfAttachment.pullback ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment.pullback

def SmoothSelfAttachment.pullbackEquiv : ClosedOrientedManifold.OrientedDiffeomorph
    (SmoothSelfAttachment.pullback c d c' d' hcd hcd' a F hc hd s).toConnectedClosedOrientedManifold.toClosedOrientedManifold
    s.toConnectedClosedOrientedManifold.toClosedOrientedManifold := by
  let E := s.toConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph
    (SelfAttachment.homeomorphOfChartTransport c.toBallChart d.toBallChart c'.toBallChart d'.toBallChart
      hcd hcd' F.val.toHomeomorph hc hd a.val.toHomeomorph)
  exact ⟨E.val, E.property⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SmoothSelfAttachment.pullbackEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SmoothSelfAttachment.pullbackEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SmoothSelfAttachment.pullbackEquiv ``Submission.DifferentialGeometry.Topology.SmoothSelfAttachment.pullbackEquiv

end DifferentialGeometry.Topology
