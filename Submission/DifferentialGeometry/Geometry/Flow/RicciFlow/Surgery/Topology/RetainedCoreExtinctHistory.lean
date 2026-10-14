import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionAssembly
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_poincare_controlled_extinction_of_retainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (H : RetainedCoreHistory
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold))
    (A : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory)
    (hbfr : ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing)
    (hctrl : ∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  letI : Nonempty
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Carrier :=
    inferInstanceAs (Nonempty M.Carrier)
  exists_poincare_controlled_extinction_of_observedHistory
    (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory A
    (fun i => (RetainedCoreEvent.toMetricCutCapEvent_hasCutCapCompletion (H.coreEvent i)
      (hbfr i)).some)
    (fun i =>
      RetainedCoreEvent.toMetricCutCapEvent_coreInclusionIsSmoothEmbedding (H.coreEvent i))
    (fun i => hctrl i)
    hempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_retainedCoreHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_retainedCoreHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_retainedCoreHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_retainedCoreHistory

theorem RetainedCoreHistory.eventCount_pos_of_final_empty {P : OrientedThreeStage.{u}}
    {g : P.Metric} [Nonempty P.Carrier] (H : RetainedCoreHistory P)
    (A : InitialIdentification P g H.toHistory)
    (hempty : IsEmpty (H.stage (Fin.last H.eventCount)).Carrier) : 0 < H.eventCount :=
  @ObservedHistory.eventCount_pos_of_final_empty H.toHistory A.initial_nonempty hempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventCount_pos_of_final_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventCount_pos_of_final_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventCount_pos_of_final_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.eventCount_pos_of_final_empty

namespace ObservedHistory

theorem isEmpty_stage_last_of_restrict_last {H : ObservedHistory.{u}}
    (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (h : IsEmpty ((H.restrict t).stage (Fin.last (H.restrict t).eventCount)).Carrier) :
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  have he : (H.restrict t).stage (Fin.last (H.restrict t).eventCount) =
      H.stage (H.activeStage t) := rfl
  rw [he] at h
  have hlast : H.activeStage t = Fin.last H.eventCount := H.empty_stage_is_last (H.activeStage t)
  rw [hlast] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isEmpty_stage_last_of_restrict_last then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isEmpty_stage_last_of_restrict_last"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isEmpty_stage_last_of_restrict_last ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.isEmpty_stage_last_of_restrict_last

end ObservedHistory

def HasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ (H : RetainedCoreHistory
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold))
    (_ : InitialIdentification
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g H.toHistory),
    (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
    (∀ i : Fin H.eventCount,
      (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasExtinctRetainedCoreHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasExtinctRetainedCoreHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasExtinctRetainedCoreHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasExtinctRetainedCoreHistory

theorem exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasExtinctRetainedCoreHistory M g) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) := by
  obtain ⟨H, A, hbfr, hctrl, hempty⟩ := h
  exact exists_poincare_controlled_extinction_of_retainedCoreHistory M g H A hbfr hctrl hempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory

theorem hext_of_hasExtinctRetainedCoreHistory
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasExtinctRetainedCoreHistory M g) :
    ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  fun M hsc g =>
    let _ := hsc
    exists_poincare_controlled_extinction_of_hasExtinctRetainedCoreHistory M g (h M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasExtinctRetainedCoreHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasExtinctRetainedCoreHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasExtinctRetainedCoreHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasExtinctRetainedCoreHistory

theorem RetainedCoreObservationTower.hasExtinctRetainedCoreHistory
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (hextinct : towerExtinct T.toObservationTower) :
    HasExtinctRetainedCoreHistory M g := by
  obtain ⟨b, hb, hempty⟩ := hextinct
  refine ⟨T.history (Nat.ceil b), T.initial (Nat.ceil b), ?_, ?_, ?_⟩
  · intro i
    exact hbfr (Nat.ceil b) i
  · intro i
    exact hctrl (Nat.ceil b) i
  · refine ObservedHistory.isEmpty_stage_last_of_restrict_last
      (H := (T.history (Nat.ceil b)).toHistory) ?_ ?_
    · refine ⟨b, hb, ?_⟩
      change b ≤ (T.history (Nat.ceil b)).horizon
      rw [T.horizon_eq]
      exact Nat.le_ceil b
    · simpa only [ObservationTower.observe, ObservationTower.atIndex,
        RetainedCoreObservationTower.toObservationTower] using hempty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasExtinctRetainedCoreHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasExtinctRetainedCoreHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasExtinctRetainedCoreHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasExtinctRetainedCoreHistory

theorem exists_retainedCoreHistory_extinct_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) :
    ∃ (H : RetainedCoreHistory P) (_ : InitialIdentification P g H.toHistory),
      (∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing) ∧
      (∀ i : Fin H.eventCount,
        (H.coreEvent i).toMetricCutCapEvent.poincareStandardDiscarded) ∧
      IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  refine ⟨(RetainedCoreObservationTower.empty P g).history 0,
    (RetainedCoreObservationTower.empty P g).initial 0, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g 0) i)
  · intro i
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g 0) i)
  · have hstage : ((RetainedCoreObservationTower.empty P g).history 0).stage
        (Fin.last ((RetainedCoreObservationTower.empty P g).history 0).eventCount) = P := rfl
    rw [hstage]
    exact hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreHistory_extinct_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreHistory_extinct_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreHistory_extinct_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreHistory_extinct_of_isEmpty

theorem not_isEmpty_carrier_of_connectedClosedOrientedManifold
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) :
    ¬ IsEmpty M.Carrier :=
  not_isEmpty_iff.mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_carrier_of_connectedClosedOrientedManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_carrier_of_connectedClosedOrientedManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_carrier_of_connectedClosedOrientedManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.not_isEmpty_carrier_of_connectedClosedOrientedManifold

theorem smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory
    (hsum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasExtinctRetainedCoreHistory M g) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_poincareControlledExtinction hsum
    (hext_of_hasExtinctRetainedCoreHistory h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
