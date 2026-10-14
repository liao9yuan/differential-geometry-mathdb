import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareStandardDiscarded
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Topology (ClosedOrientedManifold ConnectedClosedOrientedManifold
  finiteConnectedSum isSphereTwoTimesCircleFactor isStandardFactor
  isStandardFactor_of_isSphereTwoTimesCircleFactor)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem isStandardFactor_of_isPositiveSpaceFormModel (h : sphericalSpaceFormCovering.{u})
    {M : ConnectedClosedOrientedManifold.{u} 3} (hM : IsPositiveSpaceFormModel M) :
    isStandardFactor M :=
  hM.elim fun g hg => Or.inl (h M g hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isStandardFactor_of_isPositiveSpaceFormModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isStandardFactor_of_isPositiveSpaceFormModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isStandardFactor_of_isPositiveSpaceFormModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.isStandardFactor_of_isPositiveSpaceFormModel

def componentwisePositiveCurvatureOrSphereProduct (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier, ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
    (∀ F ∈ L, IsPositiveSpaceFormModel F ∨ isSphereTwoTimesCircleFactor F) ∧
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph (D.component C).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwisePositiveCurvatureOrSphereProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwisePositiveCurvatureOrSphereProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwisePositiveCurvatureOrSphereProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwisePositiveCurvatureOrSphereProduct

theorem componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct
    (hround : sphericalSpaceFormCovering.{u}) {D : ClosedOrientedManifold.{u} 3}
    (h : componentwisePositiveCurvatureOrSphereProduct D) :
    D.componentwiseConnectedSumStandardFactor := by
  intro C
  obtain ⟨L, hL, hdiff⟩ := h C
  exact ⟨L, fun F hF => (hL F hF).elim
    (fun hp => isStandardFactor_of_isPositiveSpaceFormModel hround hp)
    (fun hs => isStandardFactor_of_isSphereTwoTimesCircleFactor hs), hdiff⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct

theorem MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    (hround : sphericalSpaceFormCovering.{u})
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : componentwisePositiveCurvatureOrSphereProduct E.discarded.toClosedOrientedManifold) :
    E.poincareStandardDiscarded :=
  MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor E
    (componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct hround h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct

theorem RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    (hround : sphericalSpaceFormCovering.{u})
    {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      componentwisePositiveCurvatureOrSphereProduct
        ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold) :
    T.hasPoincareStandardDiscarded :=
  RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor T
    fun n j => componentwiseConnectedSumStandardFactor_of_componentwisePositiveCurvatureOrSphereProduct
      hround (h n j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct

theorem exists_retainedCoreObservationTower_boundaryFrameReversing_hasPoincareStandardDiscarded_extinct
    (P : OrientedThreeStage.{u}) [IsEmpty P.Carrier] (g : P.Metric) :
    ∃ T : RetainedCoreObservationTower P g, T.hasBoundaryFrameReversing ∧
      T.hasPoincareStandardDiscarded ∧ towerExtinct T.toObservationTower := by
  refine ⟨RetainedCoreObservationTower.empty P g, ?_, ?_,
    RetainedCoreObservationTower.towerExtinct_empty P g⟩
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)
  · intro n j
    exact Fin.elim0 (Fin.cast (RetainedCoreObservationTower.empty_eventCount P g n) j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreObservationTower_boundaryFrameReversing_hasPoincareStandardDiscarded_extinct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreObservationTower_boundaryFrameReversing_hasPoincareStandardDiscarded_extinct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreObservationTower_boundaryFrameReversing_hasPoincareStandardDiscarded_extinct ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_retainedCoreObservationTower_boundaryFrameReversing_hasPoincareStandardDiscarded_extinct

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem hasCoreCompatibleObservationTower_of_retainedCoreTower_positiveCurvature
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (hround : sphericalSpaceFormCovering.{u})
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      componentwisePositiveCurvatureOrSphereProduct
        ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold)
    (hextinct : towerExtinct T.toObservationTower) :
    hasCoreCompatibleObservationTower M g :=
  hasCoreCompatibleObservationTower_of_retainedCoreTower_cutCap M g T hbfr
    (T.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct hround h) hextinct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_positiveCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_positiveCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_positiveCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasCoreCompatibleObservationTower_of_retainedCoreTower_positiveCurvature

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_positiveCurvature
    (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (T : RetainedCoreObservationTower (OrientedThreeStage.ofClosedOrientedManifold
      M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing)
    (hround : sphericalSpaceFormCovering.{u})
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      componentwisePositiveCurvatureOrSphereProduct
        ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold)
    (hextinct : towerExtinct T.toObservationTower) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_retainedCoreTower_cutCap M g T hbfr
    (T.hasPoincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct hround h) hextinct

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_positiveCurvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_positiveCurvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_positiveCurvature ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_positiveCurvature

end DifferentialGeometry.PDE.RicciFlow.Surgery
