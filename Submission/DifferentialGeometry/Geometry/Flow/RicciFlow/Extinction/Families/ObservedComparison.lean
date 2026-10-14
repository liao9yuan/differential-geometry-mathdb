import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ScalarComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FiniteHistory

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.Filter
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

namespace ObservedHistory

theorem eventTimes_finite (H : ObservedHistory.{u}) : H.eventTimes.Finite :=
  Set.finite_range _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_finite ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_finite

theorem eventTimes_subset_Ioc (H : ObservedHistory.{u}) :
    H.eventTimes ⊆ _root_.Set.Ioc 0 H.horizon := by
  rintro _ ⟨i, rfl⟩
  refine ⟨?_, H.time_le_horizon_at i.succ⟩
  rw [← H.time_zero]
  exact H.time_strictMono (by change 0 < i.val + 1; omega)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_subset_Ioc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_subset_Ioc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_subset_Ioc ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.eventTimes_subset_Ioc

end ObservedHistory

structure ObservedComparisonRecord (H : ObservedHistory.{u}) (c A : ℝ) where
  value : ℝ → ℝ
  hypotheses : ScalarComparisonHypotheses c H.horizon H.eventTimes value
  initial_le : value 0 ≤ A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord

namespace ObservedComparisonRecord

variable {H : ObservedHistory.{u}} {c A : ℝ}

theorem bound_nonneg (R : ObservedComparisonRecord H c A) : 0 ≤ A :=
  (R.hypotheses.nonneg 0 ⟨le_rfl, R.hypotheses.horizon_pos.le⟩).trans R.initial_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.bound_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.bound_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.bound_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.bound_nonneg

theorem horizon_le_threshold (R : ObservedComparisonRecord H c A) :
    H.horizon ≤ extinctionThreshold c A := by
  apply (scalarComparison_horizon_le_threshold R.hypotheses).trans
  apply (extinctionThreshold_strictMonoOn R.hypotheses.c_pos).monotoneOn
  · exact R.hypotheses.nonneg 0 ⟨le_rfl, R.hypotheses.horizon_pos.le⟩
  · exact R.bound_nonneg
  · exact R.initial_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.horizon_le_threshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.horizon_le_threshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.horizon_le_threshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.horizon_le_threshold

theorem isEmpty_of_threshold_lt {H : ObservedHistory.{u}} {c A : ℝ}
    (h : extinctionThreshold c A < H.horizon) :
    IsEmpty (ObservedComparisonRecord H c A) :=
  ⟨fun R => not_lt_of_ge R.horizon_le_threshold h⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.isEmpty_of_threshold_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.isEmpty_of_threshold_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.isEmpty_of_threshold_lt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.isEmpty_of_threshold_lt

theorem integrated_bound (R : ObservedComparisonRecord H c A)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc 0 H.horizon) :
    R.value t / (t + c) ^ (3 / 4 : ℝ) ≤ A / c ^ (3 / 4 : ℝ) -
      8 * Real.pi * ((t + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ)) := by
  apply (scalarComparison_integrated_bound R.hypotheses ht).trans
  exact sub_le_sub_right
    (div_le_div_of_nonneg_right R.initial_le (Real.rpow_nonneg R.hypotheses.c_pos.le _)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.integrated_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.integrated_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.integrated_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedComparisonRecord.integrated_bound

end ObservedComparisonRecord

namespace ObservedHistory

theorem final_empty_of_uniform_records (H : ObservedHistory.{u}) {c A : ℝ}
    (hH : extinctionThreshold c A < H.horizon)
    (records : ∀ _Q : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier,
      Nonempty (ObservedComparisonRecord H c A)) :
    IsEmpty (H.stage (Fin.last H.eventCount)).Carrier := by
  refine ⟨fun x => ?_⟩
  obtain ⟨R⟩ := records (ConnectedComponents.mk x)
  exact (not_lt_of_ge R.horizon_le_threshold) hH

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.final_empty_of_uniform_records then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.final_empty_of_uniform_records"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.final_empty_of_uniform_records ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.final_empty_of_uniform_records

theorem exists_extinct_prefix_of_uniform_records
    (H : ObservedHistory.{u}) {P : OrientedThreeStage.{u}} {g : P.Metric}
    [Nonempty P.Carrier] (A₀ : InitialIdentification P g H) {c A : ℝ}
    (hH : extinctionThreshold c A < H.horizon)
    (records : ∀ _Q : ConnectedComponents (H.stage (Fin.last H.eventCount)).Carrier,
      Nonempty (ObservedComparisonRecord H c A)) :
    ∃ hn : 0 < H.eventCount,
      0 < (H.toFiniteHistory hn).1.horizon ∧
      (H.toFiniteHistory hn).1.horizon ≤ H.horizon ∧
      IsEmpty ((H.toFiniteHistory hn).1.stage
        (Fin.last (H.toFiniteHistory hn).1.eventCount)).Carrier ∧
      (A₀.toFiniteHistory hn).IsPrefixOf A₀ := by
  let _ := A₀.initial_nonempty
  let _ := H.final_empty_of_uniform_records hH records
  let hn := H.eventCount_pos_of_final_empty
  refine ⟨hn, H.last_time_pos hn, H.time_le_horizon, ?_, A₀.toFiniteHistory_isPrefixOf hn⟩
  rw [H.toFiniteHistory_finalStage hn]
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_prefix_of_uniform_records then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_prefix_of_uniform_records"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_prefix_of_uniform_records ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory.exists_extinct_prefix_of_uniform_records

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
