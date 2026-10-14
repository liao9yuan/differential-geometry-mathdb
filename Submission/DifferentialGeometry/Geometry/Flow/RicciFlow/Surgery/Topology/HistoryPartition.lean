import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices

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

theorem stageDomain_subset (j : Fin (H.eventCount + 1)) :
    H.stageDomain j ⊆ _root_.Set.Icc 0 H.horizon := by
  cases j using Fin.lastCases with
  | last =>
    intro t ht
    simp only [stageDomain, Fin.lastCases_last, _root_.Set.mem_Icc] at ht
    exact ⟨(H.time_nonneg _).trans ht.1, ht.2⟩
  | cast i =>
    intro t ht
    simp only [stageDomain, Fin.lastCases_castSucc, _root_.Set.mem_Ico] at ht
    exact ⟨(H.time_nonneg _).trans ht.1, ht.2.le.trans (H.time_le_horizon_at _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain_subset ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.stageDomain_subset

theorem mem_stageDomain_iff (t : _root_.Set.Icc (0 : ℝ) H.horizon)
    (j : Fin (H.eventCount + 1)) : t.1 ∈ H.stageDomain j ↔ H.activeStage t = j := by
  constructor
  · intro ht
    cases j using Fin.lastCases with
    | last =>
      simp only [stageDomain, Fin.lastCases_last, _root_.Set.mem_Icc] at ht
      exact le_antisymm (Fin.le_last _) (H.le_activeStage t _ ht.1)
    | cast i =>
      simp only [stageDomain, Fin.lastCases_castSucc, _root_.Set.mem_Ico] at ht
      apply H.activeStage_eq_of_maximal t i.castSucc ht.1
      intro k hk
      by_contra hki
      have hnext : i.succ ≤ k := by
        change i.val + 1 ≤ k.val
        have hlt := lt_of_not_ge hki
        change i.val < k.val at hlt
        omega
      exact (not_le_of_gt ht.2) ((H.time_strictMono.monotone hnext).trans hk)
  · intro he
    rw [← he]
    exact H.activeStage_mem t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_stageDomain_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_stageDomain_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_stageDomain_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.mem_stageDomain_iff

theorem iUnion_stageDomain : (⋃ j, H.stageDomain j) = _root_.Set.Icc 0 H.horizon := by
  apply Subset.antisymm
  · exact _root_.Set.iUnion_subset fun j => H.stageDomain_subset j
  · intro t ht
    exact mem_iUnion.mpr ⟨H.activeStage ⟨t, ht⟩, H.activeStage_mem ⟨t, ht⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.iUnion_stageDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.iUnion_stageDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.iUnion_stageDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.iUnion_stageDomain

theorem pairwise_disjoint_stageDomain :
    Pairwise (fun i j => Disjoint (H.stageDomain i) (H.stageDomain j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hti htj
  let a : _root_.Set.Icc (0 : ℝ) H.horizon := ⟨t, H.stageDomain_subset i hti⟩
  exact hij (((H.mem_stageDomain_iff a i).mp hti).symm.trans
    ((H.mem_stageDomain_iff a j).mp htj))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.pairwise_disjoint_stageDomain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.pairwise_disjoint_stageDomain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.pairwise_disjoint_stageDomain ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.pairwise_disjoint_stageDomain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
