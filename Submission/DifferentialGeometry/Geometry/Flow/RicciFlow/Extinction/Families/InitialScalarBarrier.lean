import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.SlabScalarLowerBarrier
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ObservationTower
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

def InitialScalarBarrier {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) (c : ℝ) : Prop :=
  ∀ x : M, -3 / (2 * c) ≤ metricScalarAt g x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialScalarBarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialScalarBarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialScalarBarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialScalarBarrier

theorem initialScalarBarrier_of_nonnegScalarAt {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {g : SmoothRiemannianMetric ThreeModel M} {c : ℝ} (hc : 0 < c)
    (h : ∀ x : M, 0 ≤ metricScalarAt g x) : InitialScalarBarrier g c :=
  fun x =>
    (div_neg_of_neg_of_pos (by norm_num) (by positivity : (0 : ℝ) < 2 * c)).le.trans (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.initialScalarBarrier_of_nonnegScalarAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.initialScalarBarrier_of_nonnegScalarAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.initialScalarBarrier_of_nonnegScalarAt ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.initialScalarBarrier_of_nonnegScalarAt

theorem InitialIdentification.metricScalarAt_map {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H : ObservedHistory.{u}} (d : InitialIdentification P g H) (x : P.Carrier) :
    metricScalarAt (H.initialMetric 0) (d.map x) = metricScalarAt g x := by
  have hmetric : g = Diffeomorph.pullbackMetric (I := ThreeModel) (H.initialMetric 0) d.map := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact (d.metric_eq y v w).symm
  have h := DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_pullback
    (I := ThreeModel) (H.initialMetric 0) d.map x
  rw [← hmetric] at h
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.metricScalarAt_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.metricScalarAt_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.metricScalarAt_map ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.metricScalarAt_map

theorem InitialIdentification.stageZero_scalarLowerBound {P : OrientedThreeStage.{u}}
    {g : P.Metric} {H : ObservedHistory.{u}} (d : InitialIdentification P g H) {c : ℝ}
    (h : InitialScalarBarrier g c) :
    ∀ y : (H.stage 0).Carrier,
      -3 / (2 * (H.time 0 + c)) ≤ metricScalarAt (H.initialMetric 0) y := by
  intro y
  obtain ⟨x, rfl⟩ := d.map.toEquiv.surjective y
  have hmap : metricScalarAt (H.initialMetric 0) (d.map.toEquiv x) = metricScalarAt g x :=
    d.metricScalarAt_map x
  rw [hmap, H.time_zero, zero_add]
  exact h x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.stageZero_scalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.stageZero_scalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.stageZero_scalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.stageZero_scalarLowerBound

theorem InitialIdentification.historyScalarLowerBound {P : OrientedThreeStage.{u}} {g : P.Metric}
    {H : ObservedHistory.{u}} (d : InitialIdentification P g H) {parameters : CutoffParameters}
    (cutoff : ∀ i : Fin H.eventCount, GeometricCutoffRecord H i parameters)
    {c : ℝ} (hc : 0 < c) (h : InitialScalarBarrier g c) :
    HistoryScalarLowerBound H c :=
  (DifferentialGeometry.PDE.RicciFlow.historyScalarLowerBound_of_history cutoff hc
    (d.stageZero_scalarLowerBound h)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.historyScalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.historyScalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.historyScalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.InitialIdentification.historyScalarLowerBound

theorem ObservationTower.historyScalarLowerBound_of_initialScalarBarrier
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c) (h : InitialScalarBarrier g c) :
    ∀ (b : ℝ) (hb : 0 < b), HistoryScalarLowerBound (T.observe b hb.le) c :=
  fun b hb => (T.observeInitial b hb.le).historyScalarLowerBound (cutoff b hb) hc h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.historyScalarLowerBound_of_initialScalarBarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.historyScalarLowerBound_of_initialScalarBarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.historyScalarLowerBound_of_initialScalarBarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservationTower.historyScalarLowerBound_of_initialScalarBarrier

theorem roundThreeSphereShrinkerMetric_initialScalarBarrier {c : ℝ} (hc : 0 < c) :
    InitialScalarBarrier DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric c := by
  intro x
  rw [DifferentialGeometry.Geometry.roundThreeSphereShrinkerMetric_scalarCurvature x]
  exact (div_neg_of_neg_of_pos (by norm_num) (by positivity : (0 : ℝ) < 2 * c)).le.trans
    (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundThreeSphereShrinkerMetric_initialScalarBarrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundThreeSphereShrinkerMetric_initialScalarBarrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundThreeSphereShrinkerMetric_initialScalarBarrier ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.roundThreeSphereShrinkerMetric_initialScalarBarrier

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
