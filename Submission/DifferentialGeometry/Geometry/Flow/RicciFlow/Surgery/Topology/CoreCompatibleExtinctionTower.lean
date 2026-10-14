import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ControlledExtinctionTower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.OpenCoreSubmanifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

def hasCoreCompatibleEventsOfHistory (H : ObservedHistory.{u}) : Prop :=
  ∀ i : Fin H.eventCount, (H.event i).coreCompatibility

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory

def hasCoreCompatibleEvents {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) : Prop :=
  ∀ (b : ℝ) (hb : 0 ≤ b), hasCoreCompatibleEventsOfHistory (T.observe b hb)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEvents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEvents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEvents ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEvents

theorem hasCoreCompatibleEventsOfHistory_observe_zero {P : OrientedThreeStage.{u}}
    {g : P.Metric} (T : ObservationTower P g) :
    hasCoreCompatibleEventsOfHistory (T.observe 0 le_rfl) := by
  intro i
  have h : (T.observe 0 le_rfl).eventCount = 0 :=
    ObservedHistory.eventCount_eq_zero_of_horizon_zero (T.observe 0 le_rfl) rfl
  exact (h ▸ i).elim0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory_observe_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory_observe_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory_observe_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleEventsOfHistory_observe_zero

theorem isOpen_old_of_coreCompatibleEvents {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) (h : hasCoreCompatibleEvents T) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      IsOpen (((T.observe b hb).event i).old :
        Set ((T.observe b hb).event i).transition.trace.tubes.core) :=
  fun b hb i => ((T.observe b hb).event i).isOpen_old_of_coreCompatibility (h b hb i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.isOpen_old_of_coreCompatibleEvents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.isOpen_old_of_coreCompatibleEvents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.isOpen_old_of_coreCompatibleEvents ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.isOpen_old_of_coreCompatibleEvents

theorem coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : ObservationTower P g)
    (h : hasCoreCompatibleEvents T) :
    ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      letI : ChartedSpace (EuclideanHalfSpace 3) ((T.observe b hb).event i).old :=
        ((T.observe b hb).event i).oldCharts
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : ((T.observe b hb).event i).old =>
          ((T.observe b hb).event i).transition.trace.capping.coreInclusion x.1) :=
  fun b hb i =>
    ((T.observe b hb).event i).coreInclusion_isSmoothEmbedding_of_coreCompatibility (h b hb i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents

theorem hasExtinctObservationTower_of_coreCompatibleEvents
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hc : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition))
    (hcore : hasCoreCompatibleEvents T)
    (hctrl : ∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier)
    (hextinct : towerExtinct T) :
    hasExtinctObservationTower M g :=
  ⟨T, hc, coreInclusion_isSmoothEmbedding_of_coreCompatibleEvents T hcore, hctrl, hextinct⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatibleEvents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatibleEvents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatibleEvents ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatibleEvents

def hasCoreCompatibleObservationTower
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) : Prop :=
  ∃ T : ObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g,
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      Nonempty (SmoothCutCapCompletion ((T.observe b hb).event i).transition)) ∧
    hasCoreCompatibleEvents T ∧
    (∀ (b : ℝ) (hb : 0 ≤ b) (i : Fin (T.observe b hb).eventCount),
      ∀ q : ConnectedComponents ((T.observe b hb).event i).discarded.Carrier,
        DifferentialGeometry.Topology.isPoincareStandard
          (((T.observe b hb).event i).discarded.toClosedOrientedManifold.component q).Carrier) ∧
    towerExtinct T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower

theorem hasExtinctObservationTower_of_coreCompatible
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasCoreCompatibleObservationTower M g) : hasExtinctObservationTower M g := by
  obtain ⟨T, hc, hcore, hctrl, hextinct⟩ := h
  exact hasExtinctObservationTower_of_coreCompatibleEvents M g T hc hcore hctrl hextinct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatible ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_coreCompatible

theorem exists_poincare_controlled_extinction_of_coreCompatible
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (h : hasCoreCompatibleObservationTower M g) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_extinctObservationTower M g
    (hasExtinctObservationTower_of_coreCompatible M g h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_coreCompatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_coreCompatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_coreCompatible ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_coreCompatible

theorem exists_isOpenCoreSubmanifold {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) :
    ∃ (old : Type u) (oldTop : TopologicalSpace old)
      (oldCharts : ChartedSpace (EuclideanHalfSpace 3) old) (ι : old → X.trace.tubes.core),
      @IsOpenCoreSubmanifold P Q D N X old oldTop oldCharts ι :=
  ⟨↥(⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩ :
      TopologicalSpace.Opens X.trace.tubes.core),
    inferInstance, X.coreOpensCharts _, Subtype.val,
    X.isOpenCoreSubmanifold_retainedCore⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_isOpenCoreSubmanifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.exists_isOpenCoreSubmanifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_isOpenCoreSubmanifold ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.exists_isOpenCoreSubmanifold

end DifferentialGeometry.PDE.RicciFlow.Surgery
