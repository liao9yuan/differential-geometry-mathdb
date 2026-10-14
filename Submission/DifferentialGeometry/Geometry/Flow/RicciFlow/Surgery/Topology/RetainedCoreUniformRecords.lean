import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ObservedComparisonRecord
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.TowerWidthExtinction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

def UpperRightDiniSlopeBound (W : ℝ → ℝ) (c t : ℝ) : Prop :=
  ∃ m : ℝ, -3 / (4 * (t + c)) ≤ m ∧
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ _root_.Set.Ioo (0 : ℝ) δ,
      (W (t + h) - W t) / h ≤ -2 * Real.pi - m * W t + ε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.UpperRightDiniSlopeBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.UpperRightDiniSlopeBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.UpperRightDiniSlopeBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.UpperRightDiniSlopeBound

theorem upperRightDiniLE_of_slopeBound {W : ℝ → ℝ} {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t)
    (hWt : 0 ≤ W t) (h : UpperRightDiniSlopeBound W c t) :
    UpperRightDiniLE W t (-2 * Real.pi + 3 * W t / (4 * (t + c))) := by
  obtain ⟨m, hm, hbound⟩ := h
  exact DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.upperRightDiniLE_of_incrementBound
    hc ht (Filter.EventuallyEq.refl (𝓝[>] t) W) rfl hWt hm hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniLE_of_slopeBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniLE_of_slopeBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniLE_of_slopeBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniLE_of_slopeBound

theorem upperRightDiniSlopeBound_linearWeight {H : ℝ} {c t : ℝ} (hc : 0 < c)
    (hcpi : 2 * Real.pi ≤ c) (ht : t ∈ _root_.Set.Icc (0 : ℝ) H) :
    UpperRightDiniSlopeBound (fun s : ℝ => c * (H - s)) c t := by
  refine ⟨-3 / (4 * (t + c)), le_rfl, ?_⟩
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro h hh
  have hslope : (c * (H - (t + h)) - c * (H - t)) / h = -c := by
    field_simp [ne_of_gt hh.1]
    ring
  rw [hslope]
  have hden : 0 < 4 * (t + c) := by linarith [ht.1, hc]
  have hm : -3 / (4 * (t + c)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) hden.le
  have hprod : 0 ≤ -(-3 / (4 * (t + c))) * (c * (H - t)) :=
    mul_nonneg (neg_nonneg.mpr hm) (mul_nonneg hc.le (by linarith [ht.2]))
  linarith [hε, hcpi, hprod]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniSlopeBound_linearWeight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniSlopeBound_linearWeight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniSlopeBound_linearWeight ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.upperRightDiniSlopeBound_linearWeight

theorem scalarComparisonHypotheses_of_slopeBound {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (hc : 0 < c) (hH : 0 < H) (hfinite : E.Finite) (hsub : E ⊆ _root_.Set.Ioc 0 H)
    (hnonneg : ∀ t ∈ _root_.Set.Icc 0 H, 0 ≤ W t)
    (hcont : ∀ t ∈ _root_.Set.Icc 0 H, t ∉ E → ContinuousWithinAt W (_root_.Set.Icc 0 H) t)
    (hrcont : ∀ t ∈ _root_.Set.Ico 0 H, ContinuousWithinAt W (_root_.Set.Ici t) t)
    (hjump : ∀ e ∈ E, (W e : EReal) ≤ _root_.Filter.liminf (fun s => (W s : EReal)) (𝓝[<] e))
    (hslope : ∀ t ∈ _root_.Set.Ico 0 H, t ∉ E → UpperRightDiniSlopeBound W c t) :
    ScalarComparisonHypotheses c H E W where
  c_pos := hc
  horizon_pos := hH
  finite_events := hfinite
  events_subset := hsub
  nonneg := hnonneg
  continuous := hcont
  right_continuous := hrcont
  incoming_jump := hjump
  dini := fun t ht htE =>
    upperRightDiniLE_of_slopeBound hc ht.1 (hnonneg t ⟨ht.1, ht.2.le⟩) (hslope t ht htE)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonHypotheses_of_slopeBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonHypotheses_of_slopeBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonHypotheses_of_slopeBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families.scalarComparisonHypotheses_of_slopeBound

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families

universe u

def ObservationTower.UniformScalarComparisonsAbove {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (c A : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
    ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier,
      ∃ W : ℝ → ℝ,
        ScalarComparisonHypotheses c (T.observe b hb.le).horizon
          (T.observe b hb.le).eventTimes W ∧ W 0 ≤ A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformScalarComparisonsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformScalarComparisonsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformScalarComparisonsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformScalarComparisonsAbove

def ObservationTower.UniformSlopeBoundsAbove {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (c A : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
    ∀ _terminal : ConnectedComponents ((T.observe b hb.le).stage
      (Fin.last (T.observe b hb.le).eventCount)).Carrier,
      ∃ W : ℝ → ℝ,
        (∀ t ∈ _root_.Set.Icc 0 (T.observe b hb.le).horizon, 0 ≤ W t) ∧
        (∀ t ∈ _root_.Set.Icc 0 (T.observe b hb.le).horizon, t ∉ (T.observe b hb.le).eventTimes →
          ContinuousWithinAt W (_root_.Set.Icc 0 (T.observe b hb.le).horizon) t) ∧
        (∀ t ∈ _root_.Set.Ico 0 (T.observe b hb.le).horizon, ContinuousWithinAt W (_root_.Set.Ici t) t) ∧
        (∀ e ∈ (T.observe b hb.le).eventTimes,
          (W e : EReal) ≤ _root_.Filter.liminf (fun s => (W s : EReal)) (𝓝[<] e)) ∧
        (∀ t ∈ _root_.Set.Ico 0 (T.observe b hb.le).horizon, t ∉ (T.observe b hb.le).eventTimes →
          UpperRightDiniSlopeBound W c t) ∧
        W 0 ≤ A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformSlopeBoundsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformSlopeBoundsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformSlopeBoundsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.UniformSlopeBoundsAbove

theorem ObservationTower.uniformRecordsAbove_iff_uniformScalarComparisonsAbove
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) {c A : ℝ} :
    T.UniformRecordsAbove c A ↔ T.UniformScalarComparisonsAbove c A := by
  constructor
  · intro h b hb hlt terminal
    obtain ⟨R⟩ := h b hb hlt terminal
    exact ⟨R.value, R.hypotheses, R.initial_le⟩
  · intro h b hb hlt terminal
    obtain ⟨W, hW, hinit⟩ := h b hb hlt terminal
    exact ⟨{ value := W, hypotheses := hW, initial_le := hinit }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_uniformScalarComparisonsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_uniformScalarComparisonsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_uniformScalarComparisonsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_uniformScalarComparisonsAbove

theorem ObservationTower.uniformRecordsAbove_iff_isEmpty_above_threshold
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) {c A : ℝ} :
    T.UniformRecordsAbove c A ↔
      ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
        IsEmpty ((T.observe b hb.le).stage
          (Fin.last (T.observe b hb.le).eventCount)).Carrier :=
  ⟨fun h b hb hlt => (T.records_iff_final_empty_of_threshold_lt b hb.le hlt).mp (h b hb hlt),
    T.uniformRecordsAbove_of_records_vacuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_isEmpty_above_threshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_isEmpty_above_threshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_isEmpty_above_threshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_iff_isEmpty_above_threshold

theorem ObservationTower.not_uniformRecordsAbove_of_nonempty_above_threshold
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) {c A : ℝ}
    (h : ∃ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b ∧
      Nonempty ((T.observe b hb.le).stage
        (Fin.last (T.observe b hb.le).eventCount)).Carrier) :
    ¬ T.UniformRecordsAbove c A := by
  rintro hrec
  obtain ⟨b, hb, hlt, hne⟩ := h
  exact hne.elim fun x =>
    (T.uniformRecordsAbove_iff_isEmpty_above_threshold.mp hrec b hb hlt).false x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.not_uniformRecordsAbove_of_nonempty_above_threshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.not_uniformRecordsAbove_of_nonempty_above_threshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.not_uniformRecordsAbove_of_nonempty_above_threshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.not_uniformRecordsAbove_of_nonempty_above_threshold

theorem ObservationTower.uniformRecordsAbove_of_uniformSlopeBoundsAbove
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g) {c A : ℝ}
    (hc : 0 < c) (h : T.UniformSlopeBoundsAbove c A) : T.UniformRecordsAbove c A := by
  rw [T.uniformRecordsAbove_iff_uniformScalarComparisonsAbove]
  intro b hb hlt terminal
  obtain ⟨W, hnonneg, hcont, hrcont, hjump, hslope, hinit⟩ := h b hb hlt terminal
  refine ⟨W, scalarComparisonHypotheses_of_slopeBound hc (by simpa using hb)
    (ObservedHistory.eventTimes_finite (T.observe b hb.le))
    (ObservedHistory.eventTimes_subset_Ioc (T.observe b hb.le))
    hnonneg hcont hrcont hjump hslope, hinit⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_of_uniformSlopeBoundsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_of_uniformSlopeBoundsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_of_uniformSlopeBoundsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_of_uniformSlopeBoundsAbove

theorem observedComparisonRecord_nonempty_of_slopeBound {H : ObservedHistory.{u}} {c A : ℝ}
    {W : ℝ → ℝ} (hc : 0 < c) (hH : 0 < H.horizon)
    (hnonneg : ∀ t ∈ _root_.Set.Icc 0 H.horizon, 0 ≤ W t)
    (hcont : ∀ t ∈ _root_.Set.Icc 0 H.horizon, t ∉ H.eventTimes →
      ContinuousWithinAt W (_root_.Set.Icc 0 H.horizon) t)
    (hrcont : ∀ t ∈ _root_.Set.Ico 0 H.horizon, ContinuousWithinAt W (_root_.Set.Ici t) t)
    (hjump : ∀ e ∈ H.eventTimes, (W e : EReal) ≤ _root_.Filter.liminf (fun s => (W s : EReal)) (𝓝[<] e))
    (hslope : ∀ t ∈ _root_.Set.Ico 0 H.horizon, t ∉ H.eventTimes → UpperRightDiniSlopeBound W c t)
    (hinit : W 0 ≤ A) :
    Nonempty (ObservedComparisonRecord H c A) :=
  ⟨{ value := W
     hypotheses := scalarComparisonHypotheses_of_slopeBound hc hH
       (ObservedHistory.eventTimes_finite H) (ObservedHistory.eventTimes_subset_Ioc H)
       hnonneg hcont hrcont hjump hslope
     initial_le := hinit }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_nonempty_of_slopeBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_nonempty_of_slopeBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_nonempty_of_slopeBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.observedComparisonRecord_nonempty_of_slopeBound

theorem ObservationTower.uniformRecordsAbove_empty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) (c A : ℝ) :
    (RetainedCoreObservationTower.empty P g).toObservationTower.UniformRecordsAbove c A :=
  ObservationTower.uniformRecordsAbove_of_records_vacuous _
    (fun b hb _ => by
      have h0 : IsEmpty (((RetainedCoreObservationTower.empty P g).toObservationTower.observe 0
          le_rfl).stage
          (Fin.last ((RetainedCoreObservationTower.empty P g).toObservationTower.observe 0
            le_rfl).eventCount)).Carrier :=
        ⟨fun x => hP.false x⟩
      exact @ObservationTower.empty_absorbing P g
        ((RetainedCoreObservationTower.empty P g).toObservationTower) 0 b le_rfl hb.le hb.le h0)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_empty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.uniformRecordsAbove_empty

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem hasCoreCompatibleObservationTower_of_retainedCoreTower_uniformRecordsAbove
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (hrec : T.toObservationTower.UniformRecordsAbove c A) :
    hasCoreCompatibleObservationTower M g :=
  hasCoreCompatibleObservationTower_of_retainedCoreTower_cutCap M g T hbfr hctrl
    (T.toObservationTower.towerExtinct_of_uniformRecordsAbove hrec)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_uniformRecordsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_uniformRecordsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_uniformRecordsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_uniformRecordsAbove

theorem hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (hrec : T.toObservationTower.UniformRecordsAbove c A) :
    hasExtinctObservationTower M g :=
  hasExtinctObservationTower_of_retainedCoreTower_cutCap M g T hbfr hctrl
    (T.toObservationTower.towerExtinct_of_uniformRecordsAbove hrec)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove

theorem hasExtinctObservationTower_of_retainedCoreTower_uniformScalarComparisonsAbove
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (h : T.toObservationTower.UniformScalarComparisonsAbove c A) :
    hasExtinctObservationTower M g :=
  hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove M g T hbfr hctrl
    (T.toObservationTower.uniformRecordsAbove_iff_uniformScalarComparisonsAbove.mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformScalarComparisonsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformScalarComparisonsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformScalarComparisonsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformScalarComparisonsAbove

theorem hasExtinctObservationTower_of_retainedCoreTower_uniformSlopeBoundsAbove
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (hc : 0 < c) (h : T.toObservationTower.UniformSlopeBoundsAbove c A) :
    hasExtinctObservationTower M g :=
  hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove M g T hbfr hctrl
    (T.toObservationTower.uniformRecordsAbove_of_uniformSlopeBoundsAbove hc h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformSlopeBoundsAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformSlopeBoundsAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformSlopeBoundsAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_uniformSlopeBoundsAbove

theorem hasExtinctObservationTower_of_retainedCoreTower_isEmpty_above_threshold
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    {c A : ℝ} (h : ∀ (b : ℝ) (hb : 0 < b), extinctionThreshold c A < b →
      (T.toObservationTower.observe b hb.le).IsExtinctAtHorizon) :
    hasExtinctObservationTower M g :=
  hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove M g T hbfr hctrl
    (T.toObservationTower.uniformRecordsAbove_iff_isEmpty_above_threshold.mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_isEmpty_above_threshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_isEmpty_above_threshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_isEmpty_above_threshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_isEmpty_above_threshold

end DifferentialGeometry.PDE.RicciFlow.Surgery
