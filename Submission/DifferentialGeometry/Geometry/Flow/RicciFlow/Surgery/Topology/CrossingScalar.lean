import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import Submission.DifferentialGeometry.Geometry.Curvature.EmbeddingIsometry
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming target :: scope.openDecls } }

theorem RegularCrossing.scalar_eq
    {p : E.incoming.terminalRegularOpen} {q : Q.Carrier}
    (h : E.RegularCrossing p.val q) :
    metricScalarAt E.terminal.metric p = metricScalarAt E.outputMetric q := by
  obtain ⟨F, _, hp, heq, _, _, hmetric⟩ := h.exists_survivor_partialDiffeomorph E
  let U : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen := ⟨F.source, F.open_source⟩
  let V : _root_.TopologicalSpace.Opens Q.Carrier :=
    ⟨(F : E.incoming.terminalRegularOpen → Q.Carrier) ''
      (U : Set E.incoming.terminalRegularOpen),
      DifferentialGeometry.image_opens_isOpen F Subset.rfl⟩
  let e : U ≃ₘ⟮ThreeModel, ThreeModel⟯ V :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo F Subset.rfl
  have hmet : Diffeomorph.pullbackMetricCross (E.outputMetric.restrictOpen V) e =
      E.terminal.metric.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    have hd := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo
      F (show (U : Set E.incoming.terminalRegularOpen) ⊆ F.source from Subset.rfl) x
    change E.outputMetric.inner (F x.val) (mfderiv ThreeModel ThreeModel e x v)
      (mfderiv ThreeModel ThreeModel e x w) = _
    rw [hd v, hd w]
    exact hmetric x.val x.property v w
  have hscalar := metricScalar_cross (E.outputMetric.restrictOpen V) e ⟨p, hp⟩
  rw [hmet, metricScalarAt_restrictOpen, metricScalarAt_restrictOpen] at hscalar
  change metricScalarAt E.terminal.metric p = metricScalarAt E.outputMetric (F p) at hscalar
  simpa only [heq] using hscalar

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.scalar_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.scalar_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.scalar_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.RegularCrossing.scalar_eq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
