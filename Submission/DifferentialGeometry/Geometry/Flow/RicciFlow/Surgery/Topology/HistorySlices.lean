import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryRestriction
import Mathlib.Order.Interval.Set.Infinite

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})


theorem restrict_activeStage (a : _root_.Set.Icc (0 : ℝ) H.horizon)
    (t : _root_.Set.Icc (0 : ℝ) (H.restrict a).horizon) :
    Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1)
      ((H.restrict a).activeStage t) =
      H.activeStage ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩ := by
  symm
  apply H.activeStage_eq_of_maximal
  · exact (H.restrict a).activeStage_time_le t
  · intro k hk
    have hka : k ≤ H.activeStage a := H.le_activeStage a k (hk.trans t.2.2)
    let k' : Fin ((H.restrict a).eventCount + 1) :=
      ⟨k.val, by
        change k.val < (H.activeStage a).val + 1
        exact Nat.lt_succ_of_le hka⟩
    have hk' : (H.restrict a).time k' ≤ t.1 := hk
    exact (H.restrict a).le_activeStage t k' hk'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_activeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_activeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_activeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_activeStage

theorem restrict_stageAt (a : _root_.Set.Icc (0 : ℝ) H.horizon)
    (t : _root_.Set.Icc (0 : ℝ) (H.restrict a).horizon) :
    (H.restrict a).stageAt t = H.stageAt ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩ :=
  congrArg H.stage (H.restrict_activeStage a t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageAt

theorem stageMetric_initial (j : Fin (H.eventCount + 1)) :
    H.stageMetric j (H.time j) = H.initialMetric j := by
  cases j using Fin.lastCases with
  | last =>
    simp only [stageMetric, Fin.lastCases_last]
    split_ifs with h
    · exact H.final_initial h
    · rfl
  | cast i =>
    simpa only [stageMetric, Fin.lastCases_castSucc] using H.event_initial i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric_initial


theorem restrict_restrict_eventCount (a : _root_.Set.Icc (0 : ℝ) H.horizon)
    (t : _root_.Set.Icc (0 : ℝ) (H.restrict a).horizon) :
    ((H.restrict a).restrict t).eventCount =
      (H.restrict ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩).eventCount :=
  congrArg Fin.val (H.restrict_activeStage a t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_restrict_eventCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_restrict_eventCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_restrict_eventCount ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_restrict_eventCount


theorem restrict_horizon_eventCount :
    (H.restrict ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).eventCount = H.eventCount := by
  change (H.activeStage ⟨H.horizon, H.horizon_nonneg, le_rfl⟩).val = H.eventCount
  rw [H.activeStage_at_horizon]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon_eventCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon_eventCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon_eventCount ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon_eventCount

theorem restrict_stageMetric (a : _root_.Set.Icc (0 : ℝ) H.horizon)
    (j : Fin ((H.restrict a).eventCount + 1))
    (τ : ℝ) (hτ : τ ∈ (H.restrict a).stageDomain j) :
    HEq ((H.restrict a).stageMetric j τ)
      (H.stageMetric
        (Fin.castLE (Nat.add_le_add_right (Nat.le_of_lt_succ (H.activeStage a).isLt) 1) j) τ) := by
  cases j using Fin.lastCases with
  | cast i =>
    change HEq ((H.restrict a).stageMetric i.castSucc τ)
      (H.stageMetric (Fin.castLE (Nat.le_of_lt_succ (H.activeStage a).isLt) i).castSucc τ)
    simp only [stageMetric, Fin.lastCases_castSucc]
    rfl
  | last =>
    simp only [stageDomain, Fin.lastCases_last, Set.mem_Icc] at hτ
    simp only [stageMetric, Fin.lastCases_last]
    change H.time (H.activeStage a) ≤ τ ∧ τ ≤ a.1 at hτ
    change HEq
      ((if h : H.time (H.activeStage a) < a.1 then
        (H.closedPrefixAt a h).flow.base.metric
      else fun _ => H.initialMetric (H.activeStage a)) τ)
      (H.stageMetric (H.activeStage a) τ)
    split_ifs with h
    · exact heq_of_eq (H.closedPrefixAt_metric a h τ)
    · have he : τ = H.time (H.activeStage a) :=
        le_antisymm (hτ.2.trans (not_lt.mp h)) hτ.1
      subst τ
      exact heq_of_eq (H.stageMetric_initial _).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stageMetric

theorem activeStage_mem (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    t.1 ∈ H.stageDomain (H.activeStage t) := by
  have hleft := H.activeStage_time_le t
  generalize he : H.activeStage t = k at hleft ⊢
  cases k using Fin.lastCases with
  | last =>
    simpa only [stageDomain, Fin.lastCases_last, Set.mem_Icc] using And.intro hleft t.2.2
  | cast i =>
    simp only [stageDomain, Fin.lastCases_castSucc, Set.mem_Ico]
    change H.time i.castSucc ≤ t.1 ∧ t.1 < H.time i.succ
    refine ⟨hleft, ?_⟩
    have hk : (H.activeStage t).val < H.eventCount := by rw [he]; exact i.isLt
    have hn := H.activeStage_before_next t hk
    have hi : (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = i.succ := by
      apply Fin.ext
      change (H.activeStage t).val + 1 = i.val + 1
      have hv := congrArg Fin.val he
      exact congrArg (· + 1) hv
    simpa only [hi] using hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mem


theorem restrict_sliceMetric (a : _root_.Set.Icc (0 : ℝ) H.horizon)
    (t : _root_.Set.Icc (0 : ℝ) (H.restrict a).horizon) :
    HEq ((H.restrict a).stageMetric ((H.restrict a).activeStage t) t.1)
      (H.stageMetric (H.activeStage ⟨t.1, t.2.1, t.2.2.trans a.2.2⟩) t.1) := by
  have he := H.restrict_activeStage a t
  have hm := H.restrict_stageMetric a ((H.restrict a).activeStage t) t.1
    ((H.restrict a).activeStage_mem t)
  rw [he] at hm
  exact hm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_sliceMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_sliceMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_sliceMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_sliceMetric

theorem exists_time_mem_Ioo_ne_event_times
    {a b : ℝ} (hab : a < b) :
    ∃ τ ∈ _root_.Set.Ioo a b, ∀ j : Fin (H.eventCount + 1), τ ≠ H.time j := by
  obtain ⟨τ, hτ, hnot⟩ := (_root_.Set.Ioo_infinite hab).exists_notMem_finite (Set.finite_range H.time)
  exact ⟨τ, hτ, fun j hj => hnot ⟨j, hj.symm⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_time_mem_Ioo_ne_event_times then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_time_mem_Ioo_ne_event_times"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_time_mem_Ioo_ne_event_times ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_time_mem_Ioo_ne_event_times

theorem mem_event_slab_or_after_stage_of_ne_time
    (first last : Fin (H.eventCount + 1))
    {τ s : ℝ} (hτ : τ ∈ _root_.Set.Ioo (H.time first) s)
    (hne : ∀ j : Fin (H.eventCount + 1), τ ≠ H.time j) :
    (∃ next : Fin H.eventCount, first ≤ next.castSucc ∧ next.succ ≤ last ∧
      τ ∈ _root_.Set.Ioo (H.time next.castSucc) (H.time next.succ)) ∨
      τ ∈ _root_.Set.Ioo (H.time last) s := by
  by_cases hlast : H.time last < τ
  · exact Or.inr ⟨hlast, hτ.2⟩
  have hbefore : τ < H.time last := lt_of_le_of_ne (le_of_not_gt hlast) (hne last)
  let t : _root_.Set.Icc (0 : ℝ) H.horizon :=
    ⟨τ, (H.time_nonneg first).trans hτ.1.le,
      hbefore.le.trans (H.time_le_horizon_at last)⟩
  have hk : H.activeStage t < last :=
    H.time_strictMono.lt_iff_lt.mp ((H.activeStage_time_le t).trans_lt hbefore)
  have hkval : (H.activeStage t).val < H.eventCount := by
    have := last.isLt
    have : (H.activeStage t).val < last.val := hk
    omega
  let next : Fin H.eventCount := ⟨(H.activeStage t).val, hkval⟩
  refine Or.inl ⟨next, H.le_activeStage t first hτ.1.le, ?_, ?_, ?_⟩
  · change (H.activeStage t).val + 1 ≤ last.val
    exact hk
  · exact lt_of_le_of_ne (H.activeStage_time_le t) (Ne.symm (hne (H.activeStage t)))
  · exact H.activeStage_before_next t hkval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_event_slab_or_after_stage_of_ne_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_event_slab_or_after_stage_of_ne_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_event_slab_or_after_stage_of_ne_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_event_slab_or_after_stage_of_ne_time

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
