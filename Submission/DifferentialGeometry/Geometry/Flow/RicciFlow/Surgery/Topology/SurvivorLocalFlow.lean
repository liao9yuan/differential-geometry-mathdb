import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s b : ℝ} (E : MetricCutCapEvent P Q a s)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming : SigmaCompactSpace E.incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      E.incoming.terminalRegularOpen.isOpen)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.instSigmaCompactSpaceSubtypeCarrierMemOpensTerminalRegularOpenIncoming target :: scope.openDecls } }

theorem exists_survivor_local_flow
    (G : Q.IncomingSlab s b) (hmetric : G.flow.base.metric s = E.outputMetric)
    (W : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen) (x₀ : W)
    (hW : ∀ x ∈ W, x.val ∈ interior (Subtype.val '' E.old)) :
    let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
    ∃ (F : PartialDiffeomorph ThreeModel ThreeModel
          E.incoming.terminalRegularOpen Q.Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closedOpen s b G.lt)),
      F.source = W ∧ IsSolutionOn S ∧
      (∀ x ∈ W, E.RegularCrossing x.val (F x)) ∧
      S.base.metric s = E.terminal.metric.restrictOpen W ∧
      (∀ t (x : W) (v w : TangentSpace ThreeModel x),
        (S.base.metric t).inner x v w =
          (G.flow.base.metric t).inner (F x)
            (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w)) := by
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  obtain ⟨F, hsource, hcross, _, hinner⟩ := E.exists_survivor_partialDiffeomorph W x₀ hW
  obtain ⟨S, hS, hpull⟩ := exists_local_solution_of_partialDiffeomorph G.flow G.equation F W
    (by rw [hsource])
  have hstart : S.base.metric s = E.terminal.metric.restrictOpen W := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [hpull, hmetric]
    exact hinner x.val x.property v w
  exact ⟨F, S, hsource, hS, hcross, hstart, hpull⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow

variable {V XH X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace XH] {I : ModelWithCorners ℝ V XH} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace XH X]

theorem exists_survivor_local_flow_of_regularCrossing_chart
    (G : Q.IncomingSlab s b) (hmetric : G.flow.base.metric s = E.outputMetric)
    (φ : X → E.incoming.terminalRegularOpen) (ψ : X → Q.Carrier)
    (hφ : _root_.Manifold.IsSmoothEmbedding I ThreeModel ∞ φ)
    (hdim : Module.finrank ℝ V = Module.finrank ℝ ThreeSpace)
    (hcross : ∀ x, E.RegularCrossing (φ x).val (ψ x)) (x₀ : X) :
    let W : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
      ⟨range φ, Manifold.isOpen_range_of_isSmoothEmbedding hdim hφ⟩
    letI : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
    ∃ (F : PartialDiffeomorph ThreeModel ThreeModel
          E.incoming.terminalRegularOpen Q.Carrier ∞)
      (S : SolutionOn (I := ThreeModel) (M := W) (RealTimeInterval.closedOpen s b G.lt)),
      F.source = W ∧ ψ = (F : _ → _) ∘ φ ∧ IsSolutionOn S ∧
      S.base.metric s = E.terminal.metric.restrictOpen W ∧
      ∀ t (x : W) (v w : TangentSpace ThreeModel x),
        (S.base.metric t).inner x v w =
          (G.flow.base.metric t).inner (F x)
            (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w) := by
  let W : _root_.TopologicalSpace.Opens E.incoming.terminalRegularOpen :=
    ⟨range φ, Manifold.isOpen_range_of_isSmoothEmbedding hdim hφ⟩
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  obtain ⟨F, hsource, hψ, hinner⟩ :=
    E.exists_survivor_partialDiffeomorph_of_regularCrossing_chart φ ψ hφ hdim hcross x₀
  obtain ⟨S, hS, hpull⟩ := exists_local_solution_of_partialDiffeomorph G.flow G.equation F W
    (by rw [hsource]; exact Subset.rfl)
  have hstart : S.base.metric s = E.terminal.metric.restrictOpen W := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [hpull, hmetric]
    exact hinner x.val (by rw [hsource]; exact x.property) v w
  exact ⟨F, S, hsource, hψ, hS, hstart, hpull⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow_of_regularCrossing_chart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow_of_regularCrossing_chart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow_of_regularCrossing_chart ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.exists_survivor_local_flow_of_regularCrossing_chart

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent
