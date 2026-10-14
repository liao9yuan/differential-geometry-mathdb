import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ExtinctionExistenceReduction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservationTower

theorem eventCount_observe_natCast {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (n : ℕ) :
    (T.observe (n : ℝ) (Nat.cast_nonneg n)).eventCount = (T.history n).eventCount := by
  have h0 := (T.observe_eq_atIndex n (n : ℝ) (Nat.cast_nonneg n)
    le_rfl).count_eq
  have h1 : (T.atIndex n (n : ℝ) (Nat.cast_nonneg n) le_rfl).eventCount =
      ((T.history n).restrict ⟨(T.history n).horizon, (T.history n).horizon_nonneg,
        le_rfl⟩).eventCount :=
    congrArg (fun t : _root_.Set.Icc (0 : ℝ) (T.history n).horizon =>
      ((T.history n).restrict t).eventCount) (Subtype.ext (T.horizon_eq n).symm)
  have h2 : ((T.history n).restrict ⟨(T.history n).horizon, (T.history n).horizon_nonneg,
      le_rfl⟩).eventCount = (T.history n).eventCount := by
    rw [ObservedHistory.restrict_eventCount, ObservedHistory.activeStage_at_horizon]
    rfl
  exact h0.trans (h1.trans h2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_natCast then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_natCast"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_natCast ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_natCast

theorem eventCount_observe_eq_zero {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (h : ∀ n : ℕ, (T.history n).eventCount = 0)
    (b : ℝ) (hb : 0 ≤ b) : (T.observe b hb).eventCount = 0 := by
  rw [ObservationTower.observe, ObservationTower.atIndex, ObservedHistory.restrict_eventCount]
  have hbound := Fin.isLt ((T.history (Nat.ceil b)).activeStage
    ⟨b, hb, by rw [T.horizon_eq]; exact Nat.le_ceil b⟩)
  have hzero : (T.history (Nat.ceil b)).eventCount = 0 := h (Nat.ceil b)
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.eventCount_observe_eq_zero

end ObservationTower

namespace RetainedCoreHistory

def ofClosedSlab {P : OrientedThreeStage.{u}} (g : P.Metric) {T : ℝ} (hT : 0 < T)
    (S : P.ClosedSlab 0 T) (hS : S.flow.base.metric 0 = g) : RetainedCoreHistory P where
  horizon := T
  horizon_nonneg := hT.le
  eventCount := 0
  time := fun _ => 0
  time_strictMono := by
    intro i j hij
    omega
  time_zero := rfl
  time_le_horizon := by simpa using hT.le
  stage := fun _ => P
  initialMetric := fun _ => g
  coreEvent i := Fin.elim0 i
  event_initial i := Fin.elim0 i
  event_output i := Fin.elim0 i
  finalSlab := fun _ => S
  final_initial := fun _ => hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.ofClosedSlab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.ofClosedSlab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.ofClosedSlab ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory.ofClosedSlab

end RetainedCoreHistory

namespace RetainedCoreObservationTower

def EventFree {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) : Prop :=
  ∀ n : ℕ, (T.history n).eventCount = 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.EventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.EventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.EventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.EventFree

def HasUniformCutoffRecordsAt {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (parameters : ℝ → CutoffParameters) : Prop :=
  Nonempty (∀ (b : ℝ) (hb : 0 < b)
    (i : Fin (T.toObservationTower.observe b hb.le).eventCount),
    GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecordsAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecordsAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecordsAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecordsAt

def HasUniformCutoffRecords {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) : Prop :=
  ∃ parameters : ℝ → CutoffParameters, T.HasUniformCutoffRecordsAt parameters

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecords then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecords"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecords ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformCutoffRecords

theorem eventCount_observe_eq_zero {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (h : T.EventFree) (b : ℝ) (hb : 0 ≤ b) :
    (T.toObservationTower.observe b hb).eventCount = 0 :=
  ObservationTower.eventCount_observe_eq_zero T.toObservationTower (fun n => h n) b hb

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventCount_observe_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventCount_observe_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventCount_observe_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventCount_observe_eq_zero

theorem eventFree_iff_observe_eventCount_eq_zero {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) :
    T.EventFree ↔ ∀ (b : ℝ) (hb : 0 ≤ b),
      (T.toObservationTower.observe b hb).eventCount = 0 := by
  constructor
  · intro h b hb
    exact T.eventCount_observe_eq_zero h b hb
  · intro h n
    have hobs := h (n : ℝ) (Nat.cast_nonneg n)
    rwa [ObservationTower.eventCount_observe_natCast] at hobs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventFree_iff_observe_eventCount_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventFree_iff_observe_eventCount_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventFree_iff_observe_eventCount_eq_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.eventFree_iff_observe_eventCount_eq_zero

theorem history_zero_eventCount {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) : (T.history 0).eventCount = 0 :=
  ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.history 0).toHistory
    (by simpa using T.horizon_eq 0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.history_zero_eventCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.history_zero_eventCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.history_zero_eventCount ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.history_zero_eventCount

theorem hasBoundaryFrameReversing_of_eventFree {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (h : T.EventFree) :
    T.hasBoundaryFrameReversing := by
  intro n j
  have hzero : (T.history n).eventCount = 0 := h n
  rw [hzero] at j
  exact Fin.elim0 j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasBoundaryFrameReversing_of_eventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasBoundaryFrameReversing_of_eventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasBoundaryFrameReversing_of_eventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasBoundaryFrameReversing_of_eventFree

theorem hasPoincareStandardDiscarded_of_eventFree {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : RetainedCoreObservationTower P g) (h : T.EventFree) :
    T.hasPoincareStandardDiscarded := by
  intro n j
  have hzero : (T.history n).eventCount = 0 := h n
  rw [hzero] at j
  exact Fin.elim0 j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_eventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_eventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_eventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_eventFree

theorem hasUniformCutoffRecordsAt_of_eventFree {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (h : T.EventFree)
    (parameters : ℝ → CutoffParameters) : T.HasUniformCutoffRecordsAt parameters :=
  ⟨fun b hb i => Fin.elim0 (T.eventCount_observe_eq_zero h b hb.le ▸ i)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecordsAt_of_eventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecordsAt_of_eventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecordsAt_of_eventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecordsAt_of_eventFree

theorem hasUniformCutoffRecords_of_eventFree {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (h : T.EventFree) :
    T.HasUniformCutoffRecords :=
  ⟨fun _ => Classical.choice nonempty_cutoffParameters,
    T.hasUniformCutoffRecordsAt_of_eventFree h _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecords_of_eventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecords_of_eventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecords_of_eventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasUniformCutoffRecords_of_eventFree

end RetainedCoreObservationTower

namespace GeometricCutoffRecord

def ofUniformCutoffRecords {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : RetainedCoreObservationTower P g} (h : T.HasUniformCutoffRecords)
    (b : ℝ) (hb : 0 < b)
    (i : Fin (T.toObservationTower.observe b hb.le).eventCount) :
    GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (Classical.choose h b) :=
  Classical.choice (Classical.choose_spec h) b hb i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofUniformCutoffRecords then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofUniformCutoffRecords"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofUniformCutoffRecords ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord.ofUniformCutoffRecords

end GeometricCutoffRecord

def HasEventFreeSurgeryTower (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ T : RetainedCoreObservationTower P g, T.EventFree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasEventFreeSurgeryTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasEventFreeSurgeryTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasEventFreeSurgeryTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasEventFreeSurgeryTower

theorem hasSurgeryContinuationTower_of_eventFree
    {P : OrientedThreeStage.{u}} {g : P.Metric} (h : HasEventFreeSurgeryTower P g) :
    HasSurgeryContinuationTower P g := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨parameters, hrecords⟩ := T.hasUniformCutoffRecords_of_eventFree hT
  exact ⟨T, parameters, Classical.choice hrecords, T.hasBoundaryFrameReversing_of_eventFree hT,
    T.hasPoincareStandardDiscarded_of_eventFree hT⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_eventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_eventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_eventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_eventFree

theorem hasSurgeryContinuationTower_iff
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    HasSurgeryContinuationTower P g ↔
      ∃ T : RetainedCoreObservationTower P g,
        T.HasUniformCutoffRecords ∧ T.hasBoundaryFrameReversing ∧
          T.hasPoincareStandardDiscarded := by
  constructor
  · rintro ⟨T, parameters, cutoff, hbfr, hctrl⟩
    exact ⟨T, ⟨parameters, ⟨cutoff⟩⟩, hbfr, hctrl⟩
  · rintro ⟨T, ⟨parameters, hrecords⟩, hbfr, hctrl⟩
    exact ⟨T, parameters, Classical.choice hrecords, hbfr, hctrl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_iff

theorem hasSurgeryContinuationTower_of_uniformCutoffRecords
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)
    (hrecords : T.HasUniformCutoffRecords) (hbfr : T.hasBoundaryFrameReversing)
    (hctrl : T.hasPoincareStandardDiscarded) : HasSurgeryContinuationTower P g :=
  (hasSurgeryContinuationTower_iff P g).mpr ⟨T, hrecords, hbfr, hctrl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_uniformCutoffRecords then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_uniformCutoffRecords"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_uniformCutoffRecords ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_uniformCutoffRecords

theorem hasEventFreeSurgeryTower_of_isEmpty (P : OrientedThreeStage.{u})
    [IsEmpty P.Carrier] (g : P.Metric) : HasEventFreeSurgeryTower P g :=
  ⟨RetainedCoreObservationTower.empty P g, fun n =>
    RetainedCoreObservationTower.empty_eventCount P g n⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasEventFreeSurgeryTower_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasEventFreeSurgeryTower_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasEventFreeSurgeryTower_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasEventFreeSurgeryTower_of_isEmpty

theorem hasUniformCutoffRecords_empty (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier]
    (g : P.Metric) :
    (RetainedCoreObservationTower.empty P g).HasUniformCutoffRecords :=
  RetainedCoreObservationTower.hasUniformCutoffRecords_of_eventFree _
    (fun n => RetainedCoreObservationTower.empty_eventCount P g n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformCutoffRecords_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformCutoffRecords_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformCutoffRecords_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformCutoffRecords_empty

theorem hasSurgeryContinuationTower_of_isEmpty_eventFree (P : OrientedThreeStage.{u})
    [IsEmpty P.Carrier] (g : P.Metric) : HasSurgeryContinuationTower P g :=
  hasSurgeryContinuationTower_of_eventFree (hasEventFreeSurgeryTower_of_isEmpty P g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty_eventFree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty_eventFree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty_eventFree ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty_eventFree

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
