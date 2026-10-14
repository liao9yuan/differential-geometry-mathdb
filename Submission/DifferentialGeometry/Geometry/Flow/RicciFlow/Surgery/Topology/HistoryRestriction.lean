import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.History
import Mathlib.Data.Finset.Max
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

def activeStage (t : _root_.Set.Icc (0 : ℝ) H.horizon) : Fin (H.eventCount + 1) := by
  classical
  let S := Finset.univ.filter (fun j => H.time j ≤ t.1)
  have hS : S.Nonempty := ⟨0, by simp [S, H.time_zero, t.2.1]⟩
  exact S.max' hS

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage

theorem activeStage_time_le (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    H.time (H.activeStage t) ≤ t.1 := by
  classical
  let S : Finset (Fin (H.eventCount + 1)) := Finset.univ.filter (fun j => H.time j ≤ t.1)
  have hS : S.Nonempty := ⟨0, by simp [S, H.time_zero, t.2.1]⟩
  have hm : S.max' hS ∈ S := Finset.max'_mem S hS
  exact (Finset.mem_filter.mp hm).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_time_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_time_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_time_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_time_le

theorem le_activeStage (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) (hj : H.time j ≤ t.1) :
    j ≤ H.activeStage t := by
  classical
  exact Finset.le_max' _ j (by simp [hj])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_activeStage then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_activeStage"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_activeStage ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.le_activeStage

theorem activeStage_mono : Monotone H.activeStage := by
  intro t s hts
  exact H.le_activeStage s _ ((H.activeStage_time_le t).trans hts)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_mono

theorem time_nonneg (j : Fin (H.eventCount + 1)) : 0 ≤ H.time j := by
  rw [← H.time_zero]
  exact H.time_strictMono.monotone (Fin.zero_le j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_nonneg

theorem time_le_horizon_at (j : Fin (H.eventCount + 1)) : H.time j ≤ H.horizon :=
  (H.time_strictMono.monotone (Fin.le_last j)).trans H.time_le_horizon

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_le_horizon_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_le_horizon_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_le_horizon_at ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.time_le_horizon_at

theorem activeStage_at_time (j : Fin (H.eventCount + 1)) :
    H.activeStage ⟨H.time j, H.time_nonneg j, H.time_le_horizon_at j⟩ = j := by
  apply le_antisymm
  · exact H.time_strictMono.le_iff_le.mp (H.activeStage_time_le _)
  · exact H.le_activeStage _ j le_rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_time

theorem activeStage_at_horizon :
    H.activeStage ⟨H.horizon, H.horizon_nonneg, le_rfl⟩ = Fin.last H.eventCount := by
  apply le_antisymm (Fin.le_last _)
  exact H.le_activeStage _ _ H.time_le_horizon

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_horizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_horizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_horizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_at_horizon

theorem activeStage_before_next (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (h : (H.activeStage t).val < H.eventCount) :
    t.1 < H.time (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) := by
  by_contra hn
  have hle := H.le_activeStage t
    (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) (not_lt.mp hn)
  change (H.activeStage t).val + 1 ≤ (H.activeStage t).val at hle
  omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_before_next then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_before_next"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_before_next ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_before_next


abbrev stageAt (t : _root_.Set.Icc (0 : ℝ) H.horizon) : OrientedThreeStage.{u} :=
  H.stage (H.activeStage t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageAt

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
variable {P : OrientedThreeStage} {g : ℝ → P.Metric} {J K : Set ℝ}

theorem MetricSmoothUpTo.mono (hg : P.MetricSmoothUpTo g J) (hK : K ⊆ J) :
    P.MetricSmoothUpTo g K := by
  intro p t ht
  obtain ⟨U, hU, hp, hbase, V, hV, htv, A, hA, heq⟩ := hg p t (hK ht)
  refine ⟨U, hU, hp, hbase, V, hV, htv, A, hA, ?_⟩
  intro s hs x hx i j
  exact heq s ⟨hs.1, hK hs.2⟩ x hx i j

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.mono ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.MetricSmoothUpTo.mono

def IncomingSlab.closedPrefix {a s : ℝ} (G : P.IncomingSlab a s)
    (b : ℝ) (hab : a < b) (hbs : b < s) : P.ClosedSlab a b where
  lt := hab
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨ht.1, ht.2.trans_lt hbs⟩)
    (fun _ ht => ⟨ht.1, ht.2.trans hbs⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨ht.1, ht.2.trans_lt hbs⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.closedPrefix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.closedPrefix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.closedPrefix ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab.closedPrefix


def ClosedSlab.closedPrefix {a b : ℝ} (G : P.ClosedSlab a b)
    (c : ℝ) (hac : a < c) (hcb : c ≤ b) : P.ClosedSlab a c where
  lt := hac
  flow := G.flow.timeRestrict _
  equation := isSolutionOn_timeRestrict G.equation
    (fun _ ht => ⟨ht.1, ht.2.trans hcb⟩)
    (fun _ ht => ⟨ht.1, ht.2.trans_le hcb⟩)
  smoothUpTo := G.smoothUpTo.mono (fun _ ht => ⟨ht.1, ht.2.trans hcb⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.closedPrefix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.closedPrefix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.closedPrefix ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.ClosedSlab.closedPrefix

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})


def stageTime (j : Fin (H.eventCount + 1)) : _root_.Set.Icc (0 : ℝ) H.horizon :=
  ⟨H.time j, H.time_nonneg j, H.time_le_horizon_at j⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageTime

@[simp] theorem activeStage_stageTime (j : Fin (H.eventCount + 1)) :
    H.activeStage (H.stageTime j) = j := H.activeStage_at_time j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_stageTime then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_stageTime"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_stageTime ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_stageTime

theorem activeStage_eq_of_maximal (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) (hj : H.time j ≤ t.1)
    (hmax : ∀ k : Fin (H.eventCount + 1), H.time k ≤ t.1 → k ≤ j) :
    H.activeStage t = j :=
  le_antisymm (hmax _ (H.activeStage_time_le t)) (H.le_activeStage t j hj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_eq_of_maximal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_eq_of_maximal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_eq_of_maximal ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.activeStage_eq_of_maximal

def stageDomain (j : Fin (H.eventCount + 1)) : Set ℝ :=
  Fin.lastCases (_root_.Set.Icc (H.time (Fin.last H.eventCount)) H.horizon)
    (fun i => _root_.Set.Ico (H.time i.castSucc) (H.time i.succ)) j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain

def stageMetric (j : Fin (H.eventCount + 1)) : ℝ → (H.stage j).Metric :=
  Fin.lastCases
    (if h : H.time (Fin.last H.eventCount) < H.horizon then
      (H.finalSlab h).flow.base.metric
    else fun _ => H.initialMetric (Fin.last H.eventCount))
    (fun i => (H.event i).incoming.flow.base.metric) j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageMetric

private def closedPrefixOnStage (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) :
    H.time k < t.1 →
      (∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ) →
      (H.stage k).ClosedSlab (H.time k) t.1 :=
  Fin.lastCases
    (fun hleft _ =>
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2)
    (fun i hleft hright =>
      (H.event i).incoming.closedPrefix t.1 hleft (hright i rfl)) k

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage target :: scope.openDecls } }

private theorem closedPrefixOnStage_last (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (hleft : H.time (Fin.last H.eventCount) < t.1)
    (hright : ∀ i : Fin H.eventCount, Fin.last H.eventCount = i.castSucc →
      t.1 < H.time i.succ) :
    H.closedPrefixOnStage t (Fin.last H.eventCount) hleft hright =
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2 := by
  have hcomp := Fin.lastCases_last
    (motive := fun k : Fin (H.eventCount + 1) =>
      H.time k < t.1 →
        (∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ) →
        (H.stage k).ClosedSlab (H.time k) t.1)
    (last := fun hleft _ =>
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2)
    (cast := fun i hleft hright =>
      (H.event i).incoming.closedPrefix t.1 hleft (hright i rfl))
  exact congrFun (congrFun hcomp hleft) hright

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_last
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_last target :: scope.openDecls } }

private theorem closedPrefixOnStage_castSucc (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (i : Fin H.eventCount) (hleft : H.time i.castSucc < t.1)
    (hright : ∀ j : Fin H.eventCount, i.castSucc = j.castSucc → t.1 < H.time j.succ) :
    H.closedPrefixOnStage t i.castSucc hleft hright =
      (H.event i).incoming.closedPrefix t.1 hleft (hright i rfl) := by
  have hcomp := Fin.lastCases_castSucc
    (motive := fun k : Fin (H.eventCount + 1) =>
      H.time k < t.1 →
        (∀ j : Fin H.eventCount, k = j.castSucc → t.1 < H.time j.succ) →
        (H.stage k).ClosedSlab (H.time k) t.1)
    (last := fun hleft _ =>
      (H.finalSlab (hleft.trans_le t.2.2)).closedPrefix t.1 hleft t.2.2)
    (cast := fun j hleft hright =>
      (H.event j).incoming.closedPrefix t.1 hleft (hright j rfl)) i
  exact congrFun (congrFun hcomp hleft) hright

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_castSucc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_castSucc target :: scope.openDecls } }
private theorem closedPrefixOnStage_initial (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) (hleft : H.time k < t.1)
    (hright : ∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ) :
    (H.closedPrefixOnStage t k hleft hright).flow.base.metric (H.time k) =
      H.initialMetric k := by
  cases k using Fin.lastCases with
  | last =>
    rw [H.closedPrefixOnStage_last]
    change (H.finalSlab (hleft.trans_le t.2.2)).flow.base.metric
      (H.time (Fin.last H.eventCount)) = H.initialMetric (Fin.last H.eventCount)
    exact H.final_initial (hleft.trans_le t.2.2)
  | cast i =>
    rw [H.closedPrefixOnStage_castSucc]
    change (H.event i).incoming.flow.base.metric (H.time i.castSucc) = H.initialMetric i.castSucc
    exact H.event_initial i

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_initial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_initial target :: scope.openDecls } }


def closedPrefixAt (t : _root_.Set.Icc (0 : ℝ) H.horizon) (h : H.time (H.activeStage t) < t.1) :
    (H.stage (H.activeStage t)).ClosedSlab (H.time (H.activeStage t)) t.1 :=
  H.closedPrefixOnStage t (H.activeStage t) h (fun i hi => by
    have hk : (H.activeStage t).val < H.eventCount := by rw [hi]; exact i.isLt
    have hn := H.activeStage_before_next t hk
    have he : (⟨(H.activeStage t).val + 1, by omega⟩ : Fin (H.eventCount + 1)) = i.succ := by
      apply Fin.ext
      change (H.activeStage t).val + 1 = i.val + 1
      have hv := congrArg Fin.val hi
      exact congrArg (· + 1) hv
    simpa only [he] using hn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt


theorem closedPrefixAt_initial (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (h : H.time (H.activeStage t) < t.1) :
    (H.closedPrefixAt t h).flow.base.metric (H.time (H.activeStage t)) =
      H.initialMetric (H.activeStage t) :=
  H.closedPrefixOnStage_initial t (H.activeStage t) h _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_initial

private theorem closedPrefixOnStage_metric (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (k : Fin (H.eventCount + 1)) (hleft : H.time k < t.1)
    (hright : ∀ i : Fin H.eventCount, k = i.castSucc → t.1 < H.time i.succ)
    (τ : ℝ) :
    (H.closedPrefixOnStage t k hleft hright).flow.base.metric τ = H.stageMetric k τ := by
  cases k using Fin.lastCases with
  | last =>
    have hf : H.time (Fin.last H.eventCount) < H.horizon := hleft.trans_le t.2.2
    rw [H.closedPrefixOnStage_last]
    simp only [stageMetric, Fin.lastCases_last, dif_pos hf]
    rfl
  | cast i =>
    rw [H.closedPrefixOnStage_castSucc]
    simp only [stageMetric, Fin.lastCases_castSucc]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixOnStage_metric target :: scope.openDecls } }

theorem closedPrefixAt_metric (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (h : H.time (H.activeStage t) < t.1) (τ : ℝ) :
    (H.closedPrefixAt t h).flow.base.metric τ = H.stageMetric (H.activeStage t) τ :=
  H.closedPrefixOnStage_metric t (H.activeStage t) h _ τ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.closedPrefixAt_metric

def restrict (t : _root_.Set.Icc (0 : ℝ) H.horizon) : ObservedHistory.{u} := by
  let k := H.activeStage t
  have hk : k.val ≤ H.eventCount := Nat.le_of_lt_succ k.isLt
  let cast : Fin (k.val + 1) → Fin (H.eventCount + 1) :=
    Fin.castLE (Nat.add_le_add_right hk 1)
  refine {
    horizon := t.1
    horizon_nonneg := t.2.1
    eventCount := k.val
    time := fun j => H.time (cast j)
    time_strictMono := fun _ _ hij => H.time_strictMono hij
    time_zero := H.time_zero
    time_le_horizon := H.activeStage_time_le t
    stage := fun j => H.stage (cast j)
    initialMetric := fun j => H.initialMetric (cast j)
    event := fun i => H.event (Fin.castLE hk i)
    event_initial := fun i => H.event_initial (Fin.castLE hk i)
    event_output := fun i => H.event_output (Fin.castLE hk i)
    finalSlab := fun h => H.closedPrefixAt t h
    final_initial := fun h => H.closedPrefixAt_initial t h }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict

@[simp] theorem restrict_horizon (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (H.restrict t).horizon = t.1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_horizon

@[simp] theorem restrict_eventCount (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (H.restrict t).eventCount = (H.activeStage t).val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventCount then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventCount"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventCount ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventCount

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u})

@[simp] theorem restrict_stage_zero (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (H.restrict t).stage 0 = H.stage 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stage_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stage_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stage_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_stage_zero

@[simp] theorem restrict_initialMetric_zero (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (H.restrict t).initialMetric 0 = H.initialMetric 0 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_initialMetric_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_initialMetric_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_initialMetric_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_initialMetric_zero

theorem restrict_event (t : _root_.Set.Icc (0 : ℝ) H.horizon) (i : Fin (H.restrict t).eventCount) :
    HEq ((H.restrict t).event i)
      (H.event (Fin.castLE (Nat.le_of_lt_succ (H.activeStage t).isLt) i)) := HEq.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_event then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_event"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_event ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_event

theorem event_reached_iff (t : _root_.Set.Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) :
    H.time i.succ ≤ t.1 ↔ i.val < (H.activeStage t).val := by
  constructor
  · intro hi
    have hh := H.le_activeStage t i.succ hi
    change i.val + 1 ≤ (H.activeStage t).val at hh
    omega
  · intro hi
    apply le_trans (H.time_strictMono.monotone ?_) (H.activeStage_time_le t)
    change i.val + 1 ≤ (H.activeStage t).val
    omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.event_reached_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.event_reached_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.event_reached_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.event_reached_iff


def eventTimes : Set ℝ := Set.range (fun i : Fin H.eventCount => H.time i.succ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes

theorem restrict_eventTimes (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (H.restrict t).eventTimes = H.eventTimes ∩ _root_.Set.Ioc 0 t.1 := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    let j : Fin H.eventCount := Fin.castLE (Nat.le_of_lt_succ (H.activeStage t).isLt) i
    refine ⟨⟨j, rfl⟩, ?_, ?_⟩
    · change 0 < H.time j.succ
      rw [← H.time_zero]
      exact H.time_strictMono (by change 0 < j.val + 1; omega)
    · exact (H.event_reached_iff t j).mpr i.isLt
  · rintro ⟨⟨i, rfl⟩, ht⟩
    exact ⟨⟨i.val, (H.event_reached_iff t i).mp ht.2⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventTimes then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventTimes"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventTimes ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.restrict_eventTimes

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification

universe u
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {H : ObservedHistory.{u}}

def restrict (A : InitialIdentification P g H) (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    InitialIdentification P g (H.restrict t) where
  map := A.map
  positive := A.positive
  metric_eq := A.metric_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict

@[simp] theorem restrict_map (A : InitialIdentification P g H) (t : _root_.Set.Icc (0 : ℝ) H.horizon) :
    (A.restrict t).map = A.map := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.restrict_map

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification
