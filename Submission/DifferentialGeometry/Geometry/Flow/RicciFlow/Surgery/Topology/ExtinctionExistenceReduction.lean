import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctHistory
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreExtinctionTimeBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreUniformRecords
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialScalarBarrier
import Mathlib.Tactic.Linarith

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

theorem exists_initialScalarBarrier_of_compact
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [IsManifold ThreeModel 1 M] [CompactSpace M] [T2Space M]
    [Nonempty M] (g : SmoothRiemannianMetric ThreeModel M) :
    ∃ c : ℝ, 0 < c ∧ InitialScalarBarrier g c := by
  obtain ⟨x₀, -, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMinOn Set.univ_nonempty
      (DifferentialGeometry.Geometry.Curvature.metricScalar_smooth g).continuous.continuousOn
  have hkey : -3 * |DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀| ≤
      2 * DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀ := by
    linarith [abs_nonneg (DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀),
      neg_le_abs (DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀)]
  refine ⟨1 / (1 + |DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀|),
    by positivity, fun x => ?_⟩
  have hx : DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀ ≤
      DifferentialGeometry.Geometry.Curvature.metricScalarAt g x := hmin (Set.mem_univ x)
  have hmid : -3 * (1 + |DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀|) / 2 ≤
      DifferentialGeometry.Geometry.Curvature.metricScalarAt g x₀ := by linarith
  rw [mul_one_div, div_div_eq_mul_div]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_compact

theorem exists_initialScalarBarrier_of_connectedClosedOrientedManifold
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    ∃ c : ℝ, 0 < c ∧ InitialScalarBarrier g c :=
  letI : Nonempty M.Carrier := M.connected.toNonempty
  exists_initialScalarBarrier_of_compact g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_connectedClosedOrientedManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_connectedClosedOrientedManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_connectedClosedOrientedManifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_initialScalarBarrier_of_connectedClosedOrientedManifold

private def scaffoldDeepRadius : ℝ :=
  _root_.Min.min (_root_.Min.min (standardCapL / 2) (standardCapRadiusOfZ (-2) / 2)) (1 / 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaffoldDeepRadius
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaffoldDeepRadius target :: scope.openDecls } }

private theorem scaffoldDeepRadius_pos : 0 < scaffoldDeepRadius :=
  lt_min (lt_min (half_pos standardCapL_pos) (half_pos (Function.invFun
    standardCapConformalCoordinate (-2 : ℝ)).2)) (by norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaffoldDeepRadius_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.scaffoldDeepRadius_pos target :: scope.openDecls } }

private def standardCapScaffoldWitness : StaticCapScaffold where
  collarLength := 1
  collar_pos := one_pos
  positiveRadius := scaffoldDeepRadius / 2
  deepRadius := scaffoldDeepRadius
  positiveRadius_pos := half_pos scaffoldDeepRadius_pos
  positive_lt_deep := half_lt_self scaffoldDeepRadius_pos
  deep_lt_one := (min_le_right _ _).trans_lt (by norm_num)
  deep_lt_cap := ((min_le_left _ _).trans (min_le_left _ _)).trans_lt
    (half_lt_self standardCapL_pos)
  deep_tip_side := by
    rw [mul_one]
    exact ((min_le_left _ _).trans (min_le_right _ _)).trans_lt
      (half_lt_self (Function.invFun standardCapConformalCoordinate (-2 : ℝ)).2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapScaffoldWitness
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.standardCapScaffoldWitness target :: scope.openDecls } }

theorem nonempty_cutoffParameters : Nonempty CutoffParameters :=
  ⟨{ delta := fun _ => 1 / 2
     neckRadius := fun _ => 1
     protectedRadius := fun _ => 1
     delta_pos := fun _ _ => by norm_num
     delta_lt_one := fun _ _ => by norm_num
     neckRadius_pos := fun _ _ => one_pos
     protectedRadius_pos := fun _ _ => one_pos
     fixed := standardCapScaffoldWitness
     modelRadius := 1
     modelRadius_pos := one_pos
     modelOrder := 0
     modelAccuracy := 1
     modelAccuracy_pos := one_pos
     recenterConstant := 4
     recenterConstant_ge_four := le_rfl }⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutoffParameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutoffParameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutoffParameters ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.nonempty_cutoffParameters

def RetainedCoreObservationTower.HasUniformHistoryScalarLowerBound
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : RetainedCoreObservationTower P g) (c : ℝ) : Prop :=
  ∀ (b : ℝ) (hb : 0 < b),
    HistoryScalarLowerBound (T.toObservationTower.observe b hb.le) c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformHistoryScalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformHistoryScalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformHistoryScalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.HasUniformHistoryScalarLowerBound

def HasSurgeryContinuationTower (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (T : RetainedCoreObservationTower P g) (parameters : ℝ → CutoffParameters)
    (_cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b)),
    T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasSurgeryContinuationTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasSurgeryContinuationTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasSurgeryContinuationTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasSurgeryContinuationTower

def HasMorganTianExtinctionInput (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (T : RetainedCoreObservationTower P g) (parameters : ℝ → CutoffParameters)
    (_cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    (c : ℝ),
    0 < c ∧ T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
      T.HasUniformHistoryScalarLowerBound c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasMorganTianExtinctionInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasMorganTianExtinctionInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasMorganTianExtinctionInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasMorganTianExtinctionInput

def HasUniformRecordsSurgeryTower (P : OrientedThreeStage.{u}) (g : P.Metric) : Prop :=
  ∃ (T : RetainedCoreObservationTower P g) (c A : ℝ),
    T.hasBoundaryFrameReversing ∧ T.hasPoincareStandardDiscarded ∧
      T.toObservationTower.UniformRecordsAbove c A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasUniformRecordsSurgeryTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasUniformRecordsSurgeryTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasUniformRecordsSurgeryTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.HasUniformRecordsSurgeryTower

theorem hasSurgeryContinuationTower_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasSurgeryContinuationTower P g := by
  obtain ⟨q⟩ := nonempty_cutoffParameters
  refine ⟨RetainedCoreObservationTower.empty P g, fun _ => q, ?_,
    (fun _ j => Fin.elim0 j), (fun _ j => Fin.elim0 j)⟩
  intro b hb i
  exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_observe_eventCount P g b hb.le) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasSurgeryContinuationTower_of_isEmpty

theorem hasMorganTianExtinctionInput_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasMorganTianExtinctionInput P g := by
  obtain ⟨q⟩ := nonempty_cutoffParameters
  refine ⟨RetainedCoreObservationTower.empty P g, fun _ => q, ?_, 1, one_pos,
    (fun _ j => Fin.elim0 j), (fun _ j => Fin.elim0 j), ?_⟩
  · intro b hb i
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_observe_eventCount P g b hb.le) i)
  · intro b hb
    exact fun _ _ x => (hP.false x).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_isEmpty

theorem hasUniformRecordsSurgeryTower_of_isEmpty (P : OrientedThreeStage.{u})
    [hP : IsEmpty P.Carrier] (g : P.Metric) : HasUniformRecordsSurgeryTower P g :=
  ⟨RetainedCoreObservationTower.empty P g, 1, 1, (fun _ j => Fin.elim0 j),
    (fun _ j => Fin.elim0 j), ObservationTower.uniformRecordsAbove_empty P g 1 1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_isEmpty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_isEmpty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_isEmpty ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_isEmpty

theorem hasMorganTianExtinctionInput_of_hasSurgeryContinuationTower
    {P : OrientedThreeStage.{u}} [Nonempty P.Carrier] {g : P.Metric}
    (h : HasSurgeryContinuationTower P g) : HasMorganTianExtinctionInput P g := by
  obtain ⟨T, parameters, cutoff, hbfr, hctrl⟩ := h
  obtain ⟨c, hc, hbarrier⟩ := exists_initialScalarBarrier_of_compact g
  exact ⟨T, parameters, cutoff, c, hc, hbfr, hctrl,
    T.toObservationTower.historyScalarLowerBound_of_initialScalarBarrier
      parameters cutoff hc hbarrier⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_hasSurgeryContinuationTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_hasSurgeryContinuationTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_hasSurgeryContinuationTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasMorganTianExtinctionInput_of_hasSurgeryContinuationTower

theorem hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasUniformRecordsSurgeryTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    HasExtinctRetainedCoreHistory M g := by
  obtain ⟨T, _c, _A, hbfr, hctrl, hrec⟩ := h
  exact RetainedCoreObservationTower.hasExtinctRetainedCoreHistory M T hbfr hctrl
    (T.toObservationTower.towerExtinct_of_uniformRecordsAbove hrec)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower

theorem hext_of_hasUniformRecordsSurgeryTower
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasUniformRecordsSurgeryTower
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  hext_of_hasExtinctRetainedCoreHistory fun M _ g =>
    hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower M g (h M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasUniformRecordsSurgeryTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasUniformRecordsSurgeryTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasUniformRecordsSurgeryTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasUniformRecordsSurgeryTower

theorem smoothPoincareConjecture_of_hasUniformRecordsSurgeryTower
    (hsum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasUniformRecordsSurgeryTower
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory hsum fun M hsc g =>
    let _ := hsc
    hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower M g (h M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasUniformRecordsSurgeryTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasUniformRecordsSurgeryTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasUniformRecordsSurgeryTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasUniformRecordsSurgeryTower

theorem hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput
    {P : OrientedThreeStage.{u}} [ConnectedSpace P.Carrier] [SimplyConnectedSpace P.Carrier]
    {g : P.Metric} (h : HasMorganTianExtinctionInput P g) :
    HasUniformRecordsSurgeryTower P g := by
  obtain ⟨T, parameters, cutoff, c, hc, hbfr, hctrl, hscalar⟩ := h
  obtain ⟨Γ₀, hrec⟩ := T.toObservationTower.uniformRecordsAbove_of_scalarLowerBound
    parameters cutoff hc hscalar
  exact ⟨T, c, Extinction.Width.familyMaximum g Γ₀.1, hbfr, hctrl, hrec⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput

theorem hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier]
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : HasMorganTianExtinctionInput
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    HasExtinctRetainedCoreHistory M g :=
  letI : ConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := M.connected
  letI : SimplyConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold).Carrier := inferInstanceAs (SimplyConnectedSpace M.Carrier)
  hasExtinctRetainedCoreHistory_of_hasUniformRecordsSurgeryTower M g
    (hasUniformRecordsSurgeryTower_of_hasMorganTianExtinctionInput h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput

theorem hext_of_hasMorganTianExtinctionInput
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasMorganTianExtinctionInput
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  hext_of_hasExtinctRetainedCoreHistory fun M hsc g =>
    let _ := hsc
    hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput M g (h M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasMorganTianExtinctionInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasMorganTianExtinctionInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasMorganTianExtinctionInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hext_of_hasMorganTianExtinctionInput

theorem smoothPoincareConjecture_of_hasMorganTianExtinctionInput
    (hsum : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount),
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition)
    (h : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier), HasMorganTianExtinctionInput
        (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_hasExtinctRetainedCoreHistory hsum fun M hsc g =>
    let _ := hsc
    hasExtinctRetainedCoreHistory_of_hasMorganTianExtinctionInput M g (h M g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasMorganTianExtinctionInput then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasMorganTianExtinctionInput"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasMorganTianExtinctionInput ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_of_hasMorganTianExtinctionInput

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
