import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCanonicalCapture
import Mathlib.Topology.Connected.LocallyConnected
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private theorem exists_scalar_time_derivative_bound (G : P.IncomingSlab a s) :
    ∃ q : ℝ, 0 < q ∧ ∃ C : ℝ≥0,
      ∀ x : P.Carrier, ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x →
        |derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x ^ 2 := by
  obtain ⟨ε, hε, hw⟩ := G.exists_all_point_canonical_neighborhoods
  obtain ⟨C1, C2, q, _, hC2, hq, hc⟩ := hw ε hε le_rfl
  refine ⟨q, hq, ⟨C2, zero_le_one.trans hC2⟩, ?_⟩
  intro x t ht hx
  exact (hc x t ⟨ht.1.le, ht.2⟩ hx.le).some.time_derivative

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_scalar_time_derivative_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.exists_scalar_time_derivative_bound target :: scope.openDecls } }


theorem TerminalLimitMetric.isCompact_scalar_sublevel
    (L : G.TerminalLimitMetric) (A : ℝ) :
    IsCompact {x : G.terminalRegularOpen | metricScalarAt L.metric x ≤ A} := by
  obtain ⟨q, hq, C, hbound⟩ := exists_scalar_time_derivative_bound G
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  exact L.isCompact_scalar_sublevel_of_time_derivative_bound hq hbound hPhi hpinch A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.isCompact_scalar_sublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.isCompact_scalar_sublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.isCompact_scalar_sublevel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.isCompact_scalar_sublevel

theorem TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (x : G.terminalRegularOpen)
    (hnoncompact : ¬ IsCompact (connectedComponent x)) (A : ℝ) :
    ∃ y ∈ connectedComponent x, A < metricScalarAt L.metric y := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  by_contra! h
  exact hnoncompact ((L.isCompact_scalar_sublevel_of_time_derivative_bound hq hbound hPhi hpinch A).of_isClosed_subset
    isClosed_connectedComponent h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound

theorem TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hnoncompact : ¬ IsCompact (connectedComponent x)) (A : ℝ) :
    ∃ y ∈ connectedComponent x, A < metricScalarAt L.metric y := by
  obtain ⟨q, hq, C, hbound⟩ := exists_scalar_time_derivative_bound G
  exact L.exists_scalar_gt_on_connectedComponent_of_not_isCompact_of_time_derivative_bound hq hbound x hnoncompact A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.exists_scalar_gt_on_connectedComponent_of_not_isCompact

theorem TerminalLimitMetric.finite_components_meeting_scalar_sublevel_of_time_derivative_bound
    (L : G.TerminalLimitMetric) {q : ℝ} {C : ℝ≥0} (hq : 0 < q)
    (hbound : ∀ x : P.Carrier, ∀ t ∈ _root_.Set.Ioo a s, q < G.flow.scalar t x →
      |derivWithin (fun v => G.flow.scalar v x) (_root_.Set.Iic t) t| ≤ C * G.flow.scalar t x ^ 2)
    (A : ℝ) :
    {c : ConnectedComponents G.terminalRegularOpen |
      ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt L.metric x ≤ A}.Finite := by
  obtain ⟨Phi, hPhi, hpinch⟩ :=
    exists_admissiblePinchingFunction_phiAlmostNonnegative_closedOpen
      G.lt G.flow G.equation (by simp [ThreeSpace])
  let : LocallyConnectedSpace G.terminalRegularOpen :=
    ChartedSpace.locallyConnectedSpace ThreeSpace G.terminalRegularOpen
  have hcompact := (L.isCompact_scalar_sublevel_of_time_derivative_bound hq hbound hPhi hpinch A).image
    ConnectedComponents.continuous_coe
  have heq : ConnectedComponents.mk '' {x : G.terminalRegularOpen |
      metricScalarAt L.metric x ≤ A} =
      {c : ConnectedComponents G.terminalRegularOpen |
        ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
          metricScalarAt L.metric x ≤ A} := by
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, rfl, hx⟩
    · rintro ⟨x, hxc, hx⟩
      exact ⟨x, hx, hxc⟩
  exact heq ▸ hcompact.finite ⟨inferInstance⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel_of_time_derivative_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel_of_time_derivative_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel_of_time_derivative_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel_of_time_derivative_bound

theorem TerminalLimitMetric.finite_components_meeting_scalar_sublevel
    (L : G.TerminalLimitMetric) (A : ℝ) :
    {c : ConnectedComponents G.terminalRegularOpen |
      ∃ x : G.terminalRegularOpen, ConnectedComponents.mk x = c ∧
        metricScalarAt L.metric x ≤ A}.Finite := by
  obtain ⟨q, hq, C, hbound⟩ := exists_scalar_time_derivative_bound G
  exact L.finite_components_meeting_scalar_sublevel_of_time_derivative_bound hq hbound A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.TerminalLimitMetric.finite_components_meeting_scalar_sublevel

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
