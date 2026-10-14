import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PinchingThroughSurgery
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DeepContinuation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowContinuationLeaf
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NoncollapsingThroughSurgeryLeaves
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodsThroughSurgeryStrong
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmallScaleNoncollapsingThroughSurgery
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedVolumeMonotone
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedVolumeLocalUpperBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingContinuationLeaf
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialRegularBlock
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCanonicalContinuationCases
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.UniformDebitSurgeryStepOfFineCutNeckSupplyStrong
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyStrongLeaf
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongNecksOfCutoffClass
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongSpatialCrossingContinuationLeaf

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem fineCutNeckSupplyStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    FineCutNeckSupplyStrong P₀ g₀ :=
  fineCutNeckSupplyStrong_holds P₀ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fineCutNeckSupplyStrong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fineCutNeckSupplyStrong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fineCutNeckSupplyStrong ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fineCutNeckSupplyStrong

theorem strongNecksOfCutoffClass (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ :=
  strongNecksOfCutoffClass_of_strongSpatialCrossing P₀ g₀
    (strongSpatialCrossingContinuation_holds P₀ g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.strongNecksOfCutoffClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.strongNecksOfCutoffClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.strongNecksOfCutoffClass ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.strongNecksOfCutoffClass

theorem uniformDebitSurgeryStepStrong (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    UniformDebitSurgeryStepStrong P₀ g₀ :=
  uniformDebitSurgeryStepStrong_of_strongNecks_of_fineCutNeckSupplyStrong P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (strongNecksOfCutoffClass P₀ g₀) (fineCutNeckSupplyStrong P₀ g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.uniformDebitSurgeryStepStrong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.uniformDebitSurgeryStepStrong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.uniformDebitSurgeryStepStrong ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.uniformDebitSurgeryStepStrong

theorem historyReducedVolumeMonotone (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeMonotone P₀ :=
  historyReducedVolumeMonotone_holds P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeMonotone

theorem historyReducedVolumeLocalUpperBound (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeLocalUpperBound P₀ :=
  historyReducedVolumeLocalUpperBound_holds P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeLocalUpperBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeLocalUpperBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeLocalUpperBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeLocalUpperBound

theorem historyReducedVolumeInitialLowerBound (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    HistoryReducedVolumeInitialLowerBound P₀ g₀ :=
  historyReducedVolumeInitialLowerBound_holds P₀ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeInitialLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeInitialLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeInitialLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.historyReducedVolumeInitialLowerBound

theorem smallScaleNoncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    SmallScaleNoncollapsingThroughSurgery P₀ g₀ :=
  smallScaleNoncollapsingThroughSurgery_of_simplyConnectedSpace P₀ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smallScaleNoncollapsingThroughSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smallScaleNoncollapsingThroughSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smallScaleNoncollapsingThroughSurgery ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smallScaleNoncollapsingThroughSurgery

theorem noncollapsingThroughSurgery (P₀ : OrientedThreeStage.{u}) [SimplyConnectedSpace P₀.Carrier]
    (g₀ : P₀.Metric) :
    NoncollapsingThroughSurgery P₀ g₀ :=
  noncollapsingThroughSurgery_of_reducedVolume_of_smallScale P₀ g₀
    (historyReducedVolumeMonotone P₀) (historyReducedVolumeLocalUpperBound P₀)
    (historyReducedVolumeInitialLowerBound P₀ g₀) (smallScaleNoncollapsingThroughSurgery P₀ g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.noncollapsingThroughSurgery then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.noncollapsingThroughSurgery"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.noncollapsingThroughSurgery ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.noncollapsingThroughSurgery

theorem crossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CrossingContinuation P₀ g₀ :=
  crossingContinuation_holds P₀ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.crossingContinuation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.crossingContinuation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.crossingContinuation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.crossingContinuation

theorem canonicalNeighborhoodContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    CanonicalNeighborhoodContinuation P₀ g₀ :=
  canonicalNeighborhoodContinuation_of_deep_of_capWindow_of_crossing P₀ g₀
    (deepContinuation P₀ g₀) (capWindowContinuation P₀ g₀) (crossingContinuation P₀ g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodContinuation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodContinuation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodContinuation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodContinuation

theorem spatialCrossingContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCrossingContinuation P₀ g₀ :=
  spatialCrossingContinuation_holds P₀ g₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCrossingContinuation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCrossingContinuation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCrossingContinuation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCrossingContinuation

theorem spatialCanonicalContinuation (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    SpatialCanonicalContinuation P₀ g₀ :=
  spatialCanonicalContinuation_of_spatialCrossing P₀ g₀ (spatialCrossingContinuation P₀ g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCanonicalContinuation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCanonicalContinuation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCanonicalContinuation ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.spatialCanonicalContinuation

theorem canonicalNeighborhoodsThroughSurgeryStrong (P₀ : OrientedThreeStage.{u})
    [SimplyConnectedSpace P₀.Carrier] (g₀ : P₀.Metric) :
    CanonicalNeighborhoodsThroughSurgeryStrong P₀ g₀ :=
  canonicalNeighborhoodsThroughSurgeryStrong_of_leaves P₀ g₀
    (pinchingThroughSurgery P₀ g₀) (noncollapsingThroughSurgery P₀ g₀)
    (canonicalNeighborhoodContinuation P₀ g₀) (spatialCanonicalContinuation P₀ g₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodsThroughSurgeryStrong then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodsThroughSurgeryStrong"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodsThroughSurgeryStrong ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.canonicalNeighborhoodsThroughSurgeryStrong

theorem exists_poincare_controlled_extinction
    (M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3)
    [SimplyConnectedSpace M.Carrier]
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) :
    Nonempty (PoincareControlledExtinction M g) := by
  have : SimplyConnectedSpace (OrientedThreeStage.ofClosedOrientedManifold M).Carrier :=
    inferInstanceAs (SimplyConnectedSpace M.Carrier)
  exact exists_poincare_controlled_extinction_of_uniformDebitSurgeryStepStrong
    (OrientedThreeStage.ofClosedOrientedManifold M) g
    (uniformDebitSurgeryStepStrong (OrientedThreeStage.ofClosedOrientedManifold M) g)
    (canonicalNeighborhoodsThroughSurgeryStrong (OrientedThreeStage.ofClosedOrientedManifold M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_poincare_controlled_extinction

theorem smoothPoincareConjecture_holds
    (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SimplyConnectedSpace M] :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := by
  obtain ⟨f⟩ := smoothPoincareConjecture_of_controlledExtinction
    (fun N _ g => exists_poincare_controlled_extinction N.toClosedOrientedManifold g) M
  exact ⟨f.trans DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.smoothPoincareConjecture_holds

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
