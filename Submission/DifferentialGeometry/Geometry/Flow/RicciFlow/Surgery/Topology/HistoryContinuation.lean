import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MaximalSlab
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricExistence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal

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

theorem RetainedCoreHistory.exists_extension_or_singular_incomingSlab
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    {B : ℝ} (hB : H.horizon < B) :
    (∃ K : RetainedCoreHistory P, K.horizon = B ∧
      H.toHistory.IsPrefixOf K.toHistory ∧ K.eventCount = H.eventCount) ∨
      ∃ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s),
        s ≤ B ∧ G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) ∧ G.SingularEndpoint := by
  have hab : H.time (Fin.last H.eventCount) < B := htime.trans_lt hB
  obtain ⟨G, hinit⟩ | ⟨s, G, hs, hinit, hsing⟩ :=
    (H.stage (Fin.last H.eventCount)).exists_closedSlab_or_singular_incomingSlab_from_time
      (H.initialMetric (Fin.last H.eventCount)) hab
  · let K := H.extendHorizon B hB.le G hinit
    have hcompat := H.extendHorizonCompatible_of_time_eq_horizon B G hinit htime
    exact Or.inl ⟨K, rfl, H.extendHorizon_isPrefixOf B hB.le G hinit hcompat, rfl⟩
  · exact Or.inr ⟨s, G, hs, hinit, hsing⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_singular_incomingSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_singular_incomingSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_singular_incomingSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_singular_incomingSlab

theorem RetainedCoreHistory.exists_extension_or_oneStepIncoming
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P)
    (htime : H.time (Fin.last H.eventCount) = H.horizon)
    (parameters : CutoffParameters) {B : ℝ} (hB : H.horizon < B) :
    (∃ K : RetainedCoreHistory P, K.horizon = B ∧
      H.toHistory.IsPrefixOf K.toHistory ∧ K.eventCount = H.eventCount) ∨
      ∃ (s : ℝ) (G : (H.stage (Fin.last H.eventCount)).IncomingSlab
          (H.time (Fin.last H.eventCount)) s)
        (L : G.TerminalLimitMetric) (D : OneStepIncoming.{u}),
        H.horizon < s ∧ s ≤ B ∧
        G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) ∧
        D.stage = H.stage (Fin.last H.eventCount) ∧
        D.startTime = H.time (Fin.last H.eventCount) ∧ D.endTime = s ∧
        HEq D.slab G ∧ HEq D.terminal L ∧ D.parameters = parameters ∧
        HEq (D.slab.flow.base.metric D.startTime) (H.initialMetric (Fin.last H.eventCount)) := by
  rcases H.exists_extension_or_singular_incomingSlab htime hB with h | ⟨s, G, hs, hinit, hsing⟩
  · exact Or.inl h
  · obtain ⟨L⟩ := G.nonempty_terminalLimitMetric
    let D : OneStepIncoming.{u} := {
      stage := H.stage (Fin.last H.eventCount)
      startTime := H.time (Fin.last H.eventCount)
      endTime := s
      startTime_nonneg := htime.symm ▸ H.horizon_nonneg
      startTime_lt_endTime := G.lt
      slab := G
      terminal := L
      singular := hsing
      parameters := parameters }
    exact Or.inr ⟨s, G, L, D, htime ▸ G.lt, hs, hinit, rfl, rfl, rfl,
      HEq.rfl, HEq.rfl, rfl, heq_of_eq hinit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_oneStepIncoming then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_oneStepIncoming"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_oneStepIncoming ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.exists_extension_or_oneStepIncoming

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
