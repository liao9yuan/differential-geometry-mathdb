import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryCompatibility

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

variable {H K L : ObservedHistory.{u}}

def IsPrefixOf (H K : ObservedHistory.{u}) : Prop :=
  ∃ h : H.horizon ≤ K.horizon,
    (K.restrict ⟨H.horizon, H.horizon_nonneg, h⟩).SamePresentation H

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf

theorem IsPrefixOf.horizon_le (h : H.IsPrefixOf K) : H.horizon ≤ K.horizon := h.choose

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.horizon_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.horizon_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.horizon_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.horizon_le

theorem IsPrefixOf.presentation (h : H.IsPrefixOf K) :
    (K.restrict ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩).SamePresentation H :=
  h.choose_spec

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.presentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.presentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.presentation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.presentation

@[refl] theorem IsPrefixOf.refl (H : ObservedHistory.{u}) : H.IsPrefixOf H :=
  ⟨le_rfl, H.restrict_self⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.refl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.refl

theorem restrict_isPrefixOf (H : ObservedHistory.{u})
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) : (H.restrict t).IsPrefixOf H :=
  ⟨t.2.2, SamePresentation.refl _⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_isPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_isPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_isPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_isPrefixOf

@[trans] theorem IsPrefixOf.trans (h : H.IsPrefixOf K) (k : K.IsPrefixOf L) :
    H.IsPrefixOf L := by
  rcases h with ⟨hHK, R⟩
  rcases k with ⟨hKL, S⟩
  let b : _root_.Set.Icc (0 : ℝ) L.horizon := ⟨K.horizon, K.horizon_nonneg, hKL⟩
  let a : _root_.Set.Icc (0 : ℝ) (L.restrict b).horizon :=
    ⟨H.horizon, H.horizon_nonneg, hHK⟩
  refine ⟨hHK.trans hKL, ?_⟩
  exact ((L.restrict_restrict b a).symm.trans
    (SamePresentation.restrict (L.restrict b) S a)).trans R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.trans ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.trans

theorem IsPrefixOf.antisymm (h : H.IsPrefixOf K) (k : K.IsPrefixOf H) :
    H.SamePresentation K := by
  have he : H.horizon = K.horizon := le_antisymm h.horizon_le k.horizon_le
  have ht : (⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩ : _root_.Set.Icc (0 : ℝ) K.horizon) =
      ⟨K.horizon, K.horizon_nonneg, le_rfl⟩ := Subtype.ext he
  have R := h.presentation
  rw [ht] at R
  exact R.symm.trans K.restrict_self

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.antisymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.antisymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.antisymm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.antisymm

theorem SamePresentation.eventTimes_eq (R : H.SamePresentation K) :
    H.eventTimes = K.eventTimes := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast R.count_eq i, ?_⟩
    exact (R.time_eq i.succ).symm
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast R.count_eq.symm i, ?_⟩
    exact (R.symm.time_eq i.succ).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.eventTimes_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.eventTimes_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.eventTimes_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.eventTimes_eq

theorem IsPrefixOf.eventTimes (h : H.IsPrefixOf K) :
    H.eventTimes = K.eventTimes ∩ _root_.Set.Ioc 0 H.horizon :=
  h.presentation.eventTimes_eq.symm.trans (K.restrict_eventTimes _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.eventTimes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.eventTimes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.eventTimes ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.eventTimes

theorem SamePresentation.stageAt_eq (R : H.SamePresentation K)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    H.stageAt t = K.stageAt
      ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩ := by
  have hstage := R.stage_eq (H.activeStage t)
  rw [SamePresentation.activeStage H R t] at hstage
  exact hstage

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageAt_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.stageAt_eq

theorem IsPrefixOf.stageAt_eq (h : H.IsPrefixOf K)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    H.stageAt t = K.stageAt ⟨t.1, t.2.1, t.2.2.trans h.horizon_le⟩ := by
  let b : _root_.Set.Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩
  exact (SamePresentation.stageAt_eq h.presentation.symm t).trans
    (K.restrict_stageAt b ⟨t.1, t.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.stageAt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.stageAt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.stageAt_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.stageAt_eq

theorem SamePresentation.sliceMetric_heq (R : H.SamePresentation K)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    HEq (H.stageMetric (H.activeStage t) t.1)
      (K.stageMetric (K.activeStage
        ⟨t.1, t.2.1, by rw [← R.horizon_eq]; exact t.2.2⟩) t.1) := by
  have hm := R.metric_heq (H.activeStage t) t.1 (H.activeStage_mem t)
  rw [SamePresentation.activeStage H R t] at hm
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.sliceMetric_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.sliceMetric_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.sliceMetric_heq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.SamePresentation.sliceMetric_heq

theorem IsPrefixOf.sliceMetric_heq (h : H.IsPrefixOf K)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    HEq (H.stageMetric (H.activeStage t) t.1)
      (K.stageMetric (K.activeStage ⟨t.1, t.2.1, t.2.2.trans h.horizon_le⟩) t.1) := by
  let b : _root_.Set.Icc (0 : ℝ) K.horizon := ⟨H.horizon, H.horizon_nonneg, h.horizon_le⟩
  exact (SamePresentation.sliceMetric_heq h.presentation.symm t).trans
    (K.restrict_sliceMetric b ⟨t.1, t.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.sliceMetric_heq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.sliceMetric_heq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.sliceMetric_heq ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.IsPrefixOf.sliceMetric_heq

theorem empty_absorbing (H : ObservedHistory.{u})
    (a b : _root_.Set.Icc (0 : ℝ) H.horizon) (hab : a.1 ≤ b.1)
    [IsEmpty (H.stageAt a).Carrier] : IsEmpty (H.stageAt b).Carrier := by
  have ha := H.empty_stage_is_last (H.activeStage a)
  have hab' : H.activeStage a ≤ H.activeStage b := H.activeStage_mono hab
  have hb : H.activeStage b = Fin.last H.eventCount := by
    apply le_antisymm (Fin.le_last _)
    simpa only [ha] using hab'
  change IsEmpty (H.stage (H.activeStage b)).Carrier
  rw [hb, ← ha]
  exact inferInstanceAs (IsEmpty (H.stageAt a).Carrier)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_absorbing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_absorbing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_absorbing ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.empty_absorbing

theorem no_event_after_empty (H : ObservedHistory.{u})
    (a : _root_.Set.Icc (0 : ℝ) H.horizon) [IsEmpty (H.stageAt a).Carrier]
    {s : ℝ} (hs : s ∈ H.eventTimes) : s ≤ a.1 := by
  obtain ⟨i, rfl⟩ := hs
  have ha := H.empty_stage_is_last (H.activeStage a)
  have ht := H.activeStage_time_le a
  rw [ha] at ht
  exact (H.time_strictMono.monotone (Fin.le_last i.succ)).trans ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.no_event_after_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.no_event_after_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.no_event_after_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.no_event_after_empty

end ObservedHistory

namespace InitialIdentification

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
variable {H K L : ObservedHistory.{u}}

def IsPrefixOf (A : InitialIdentification P g H) (B : InitialIdentification P g K) : Prop :=
  H.IsPrefixOf K ∧ HEq A.map B.map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf

@[refl] theorem IsPrefixOf.refl (A : InitialIdentification P g H) : A.IsPrefixOf A :=
  ⟨ObservedHistory.IsPrefixOf.refl H, HEq.rfl⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.refl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.refl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.refl ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.refl

@[trans] theorem IsPrefixOf.trans
    {A : InitialIdentification P g H} {B : InitialIdentification P g K}
    {C : InitialIdentification P g L} (h : A.IsPrefixOf B) (k : B.IsPrefixOf C) :
    A.IsPrefixOf C := ⟨h.1.trans k.1, h.2.trans k.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.trans then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.trans"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.trans ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.trans

theorem IsPrefixOf.antisymm
    {A : InitialIdentification P g H} {B : InitialIdentification P g K}
    (h : A.IsPrefixOf B) (k : B.IsPrefixOf A) :
    H.SamePresentation K ∧ HEq A.map B.map := ⟨h.1.antisymm k.1, h.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.antisymm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.antisymm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.antisymm ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.IsPrefixOf.antisymm

theorem restrict_isPrefixOf (A : InitialIdentification P g H)
    (t : _root_.Set.Icc (0 : ℝ) H.horizon) : (A.restrict t).IsPrefixOf A :=
  ⟨H.restrict_isPrefixOf t, HEq.rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_isPrefixOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_isPrefixOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_isPrefixOf ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_isPrefixOf

end InitialIdentification

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
