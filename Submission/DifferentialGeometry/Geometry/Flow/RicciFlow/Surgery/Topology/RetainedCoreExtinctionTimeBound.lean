import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ExtinctionTimeBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreUniformRecords

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.Families

theorem hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound
    {M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3}
    [SimplyConnectedSpace M.Carrier]
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b),
      HistoryScalarLowerBound (T.toObservationTower.observe b hb.le) c) :
    hasExtinctObservationTower M g :=
  letI : ConnectedSpace
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Carrier :=
    M.connected
  letI : SimplyConnectedSpace
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold).Carrier :=
    inferInstanceAs (SimplyConnectedSpace M.Carrier)
  (T.toObservationTower.uniformRecordsAbove_of_scalarLowerBound parameters cutoff hc hscalar).elim
    fun _ h =>
      hasExtinctObservationTower_of_retainedCoreTower_uniformRecordsAbove M g T hbfr hctrl h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound

theorem exists_poincare_controlled_extinction_of_retainedCoreTower_scalarLowerBound
    {M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3}
    [SimplyConnectedSpace M.Carrier]
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier}
    (T : RetainedCoreObservationTower
      (OrientedThreeStage.ofClosedOrientedManifold M.toClosedOrientedManifold) g)
    (hbfr : T.hasBoundaryFrameReversing) (hctrl : T.hasPoincareStandardDiscarded)
    (parameters : ℝ → CutoffParameters)
    (cutoff : ∀ (b : ℝ) (hb : 0 < b),
      ∀ i : Fin (T.toObservationTower.observe b hb.le).eventCount,
        GeometricCutoffRecord (T.toObservationTower.observe b hb.le) i (parameters b))
    {c : ℝ} (hc : 0 < c)
    (hscalar : ∀ (b : ℝ) (hb : 0 < b),
      HistoryScalarLowerBound (T.toObservationTower.observe b hb.le) c) :
    Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g) :=
  exists_poincare_controlled_extinction_of_extinctObservationTower M g
    (hasExtinctObservationTower_of_retainedCoreTower_scalarLowerBound T hbfr hctrl parameters
      cutoff hc hscalar)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_scalarLowerBound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_scalarLowerBound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_scalarLowerBound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.exists_poincare_controlled_extinction_of_retainedCoreTower_scalarLowerBound

end DifferentialGeometry.PDE.RicciFlow.Surgery
