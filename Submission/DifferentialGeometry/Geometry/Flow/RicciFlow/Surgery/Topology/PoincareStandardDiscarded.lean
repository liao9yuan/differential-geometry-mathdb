import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.PoincareControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace FiniteCutCapTrace

theorem poincareControlled_of_componentwiseConnectedSumStandardFactor (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount,
      (T.transition i).discarded.componentwiseConnectedSumStandardFactor) :
    T.poincareControlled :=
  fun i => (T.transition i).poincareControlled_of_componentwiseConnectedSumStandardFactor (h i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseConnectedSumStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseConnectedSumStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseConnectedSumStandardFactor ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseConnectedSumStandardFactor

theorem poincareControlled_of_componentwiseStandardFactor (T : FiniteCutCapTrace.{u})
    (h : ∀ i : Fin T.eventCount, (T.transition i).discarded.componentwiseStandardFactor) :
    T.poincareControlled :=
  poincareControlled_of_componentwiseConnectedSumStandardFactor T
    (fun i => componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor
      (T.transition i).discarded (h i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseStandardFactor ``Submission.DifferentialGeometry.Topology.FiniteCutCapTrace.poincareControlled_of_componentwiseStandardFactor

end FiniteCutCapTrace

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

theorem poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor
    (E : MetricCutCapEvent P Q a s)
    (h : E.discarded.toClosedOrientedManifold.componentwiseConnectedSumStandardFactor) :
    E.poincareStandardDiscarded :=
  fun q => Topology.componentwise_isPoincareStandard_of_componentwiseConnectedSumStandardFactor
    E.discarded.toClosedOrientedManifold h q

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor

theorem poincareStandardDiscarded_of_componentwiseStandardFactor
    (E : MetricCutCapEvent P Q a s)
    (h : E.discarded.toClosedOrientedManifold.componentwiseStandardFactor) :
    E.poincareStandardDiscarded :=
  poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor E
    (Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor
      E.discarded.toClosedOrientedManifold h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseStandardFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseStandardFactor

theorem poincareStandardDiscarded_of_isEmpty_discarded (E : MetricCutCapEvent P Q a s)
    [IsEmpty E.discarded.Carrier] : E.poincareStandardDiscarded := by
  have hC : IsEmpty (ConnectedComponents E.discarded.Carrier) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
  exact fun q => (hC.false q).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_isEmpty_discarded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_isEmpty_discarded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_isEmpty_discarded ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_of_isEmpty_discarded

theorem poincareStandardDiscarded_iff_transition_poincareControlled
    (E : MetricCutCapEvent P Q a s) (hc : SmoothCutCapCompletion E.transition) :
    E.poincareStandardDiscarded ↔
      (Topology.SphericalCutCapTransition.ofSmoothCutCapTransition
        E.transition hc).poincareControlled :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_iff_transition_poincareControlled then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_iff_transition_poincareControlled"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_iff_transition_poincareControlled ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent.poincareStandardDiscarded_iff_transition_poincareControlled

end MetricCutCapEvent

namespace RetainedCoreObservationTower

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor
    (T : RetainedCoreObservationTower P g)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold
        |>.componentwiseConnectedSumStandardFactor) :
    T.hasPoincareStandardDiscarded :=
  fun n j => MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor
    ((T.history n).coreEvent j).toMetricCutCapEvent (h n j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor

theorem hasPoincareStandardDiscarded_of_componentwiseStandardFactor
    (T : RetainedCoreObservationTower P g)
    (h : ∀ (n : ℕ) (j : Fin (T.history n).eventCount),
      ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold
        |>.componentwiseStandardFactor) :
    T.hasPoincareStandardDiscarded :=
  hasPoincareStandardDiscarded_of_componentwiseConnectedSumStandardFactor T
    (fun n j => Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor
      ((T.history n).coreEvent j).toMetricCutCapEvent.discarded.toClosedOrientedManifold (h n j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseStandardFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreObservationTower.hasPoincareStandardDiscarded_of_componentwiseStandardFactor

end RetainedCoreObservationTower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace FiniteSurgeryHistory

theorem poincareControlled_of_componentwiseConnectedSumStandardFactor
    (H : FiniteSurgeryHistory.{u})
    (h : ∀ i : Fin H.eventCount,
      (H.event i).transition.discarded.componentwiseConnectedSumStandardFactor) :
    H.poincareControlled :=
  fun i C => DifferentialGeometry.Topology.componentwise_isPoincareStandard_of_componentwiseConnectedSumStandardFactor
    (H.event i).transition.discarded (h i) C

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseConnectedSumStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseConnectedSumStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseConnectedSumStandardFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseConnectedSumStandardFactor

theorem poincareControlled_of_componentwiseStandardFactor (H : FiniteSurgeryHistory.{u})
    (h : ∀ i : Fin H.eventCount,
      (H.event i).transition.discarded.componentwiseStandardFactor) :
    H.poincareControlled :=
  poincareControlled_of_componentwiseConnectedSumStandardFactor H
    (fun i => DifferentialGeometry.Topology.componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor
      (H.event i).transition.discarded (h i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseStandardFactor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseStandardFactor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseStandardFactor ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.poincareControlled_of_componentwiseStandardFactor

end FiniteSurgeryHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery
