import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TowerInductionStep
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

variable {P : OrientedThreeStage.{u}} {H : RetainedCoreHistory P}
  (T : ℝ) (hT : H.horizon ≤ T)
  (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
  (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount))

private def IncomingBackwardNeck.extendHorizon
    {i : Fin H.eventCount} {δ r : ℝ} {k : ℕ}
    {neck : NormalizedNeck (H.toHistory.event i).terminal.metric δ k}
    (N : IncomingBackwardNeck H.toHistory i neck r) :
    IncomingBackwardNeck (H.extendHorizon T hT S hS).toHistory i neck r := by
  cases N
  constructor <;> assumption

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.extendHorizon
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IncomingBackwardNeck.extendHorizon target :: scope.openDecls } }

protected def GeometricCutoffRecord.extendHorizon
    {i : Fin H.eventCount} {p : CutoffParameters}
    (R : GeometricCutoffRecord H.toHistory i p) :
    GeometricCutoffRecord (H.extendHorizon T hT S hS).toHistory i p := by
  exact { R with backward := fun α => IncomingBackwardNeck.extendHorizon T hT S hS (R.backward α) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.extendHorizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.extendHorizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.extendHorizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.extendHorizon

theorem RetainedCoreHistory.boundaryFrameReversing_extendHorizon
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) :
    ∀ i : Fin (H.extendHorizon T hT S hS).eventCount,
      ((H.extendHorizon T hT S hS).coreEvent i).transition.boundaryFrameReversing := hbfr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.boundaryFrameReversing_extendHorizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.boundaryFrameReversing_extendHorizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.boundaryFrameReversing_extendHorizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.boundaryFrameReversing_extendHorizon

theorem RetainedCoreHistory.poincareStandardDiscarded_extendHorizon
    (hctrl : ∀ i : Fin H.eventCount, (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) :
    ∀ i : Fin (H.extendHorizon T hT S hS).eventCount,
      ((H.extendHorizon T hT S hS).coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded := hctrl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.poincareStandardDiscarded_extendHorizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.poincareStandardDiscarded_extendHorizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.poincareStandardDiscarded_extendHorizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.poincareStandardDiscarded_extendHorizon

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
