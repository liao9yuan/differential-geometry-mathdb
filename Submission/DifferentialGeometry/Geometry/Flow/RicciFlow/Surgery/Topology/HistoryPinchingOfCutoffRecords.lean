import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodInduction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalCapWindows
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi ∧
      ∀ (H : RetainedCoreHistory P₀), InitialIdentification P₀ g₀ H.toHistory →
      ∀ {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}, H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ →
        H.EventSlabsPinched phi ∧
        ∀ (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s),
          G.flow.base.metric (H.time k) = H.initialMetric k →
          Perelman.PhiAlmostNonnegative G.flow (_root_.Set.Ico (H.time k) s) phi := by
  obtain ⟨phi, hphi, hslab⟩ :=
    Perelman.exists_admissiblePinchingFunction_for_identified_incomingSlabs P₀ g₀
  refine ⟨phi, hphi, fun H hinit p₀ δ₀ ρ₀ hrec => ?_⟩
  obtain ⟨p, -, -, -, -, -, records, -, -, -⟩ := hrec
  exact ⟨fun j => hslab H.toHistory hinit p records j.castSucc (H.time j.succ)
      (H.toHistory.event j).incoming (H.toHistory.event_initial j),
    fun k s G hG => hslab H.toHistory hinit p records k s G hG⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_admissiblePinchingFunction_of_hasCanonicalCutoffRecords

theorem exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (H : RetainedCoreHistory P₀), InitialIdentification P₀ g₀ H.toHistory →
      ∀ {p₀ : CutoffParameters} {δ₀ ρ₀ : ℝ}, H.hasCanonicalCutoffRecords p₀ δ₀ ρ₀ →
      ∀ (k : Fin (H.eventCount + 1)) {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s),
        G.flow.base.metric (H.time k) = H.initialMetric k → G.SingularEndpoint → a ≤ s := by
  obtain ⟨a, ha, hsing⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  refine ⟨a, ha, fun H hinit p₀ δ₀ ρ₀ hrec k s G hG hs => ?_⟩
  obtain ⟨p, -, -, -, -, -, records, -, -, -⟩ := hrec
  exact hsing H.toHistory hinit (fun i => (records i).singular) k s G hG hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_pos_le_terminal_time_of_hasCanonicalCutoffRecords

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
