import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Reconstruction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.Terminal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.MetricStep
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ReducedLengthRealization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Poincare

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology _root_.Submission.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure PoincareExtinctionContracts (DiscardedCutOpen : Type u → Prop) where
  geometric : geometricReconstructionBackground.{u}
  terminalStep : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
    Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)
  metricStep : isCommonLocalRealizationOnAdmissibleStrips.{u}
  incidenceConnectedInput :
    ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (i : Fin H.eventCount) (C : ConnectedComponents (H.stage i.castSucc).Carrier),
    ((H.cutCapTrace.transition i).cutIncidenceGraph C).Connected :=
    fun H i C => H.cutCapTrace.cutIncidenceGraph_connected i C
  componentSumInput :
    ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (i : Fin H.eventCount), (H.cutCapTrace.transition i).componentConnectedSumDecomposition
  sumInput : DifferentialGeometry.Topology.poincareStandardSumClosed.{u}
  unitInput : ∀ N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3,
    Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
      (DifferentialGeometry.Topology.connectedSum N
        DifferentialGeometry.Topology.standardThreeSphereLift.{u}).toClosedOrientedManifold
      N.toClosedOrientedManifold) :=
    fun N => DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_connectedSum_sphere_right_unit N
  congruenceInput : ∀ (L K : List (DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)),
    List.Forall₂ (fun (M N : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K →
    Nonempty (DifferentialGeometry.Topology.ClosedOrientedManifold.OrientedDiffeomorph
      (DifferentialGeometry.Topology.finiteConnectedSum L).toClosedOrientedManifold
      (DifferentialGeometry.Topology.finiteConnectedSum K).toClosedOrientedManifold)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PoincareExtinctionContracts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PoincareExtinctionContracts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PoincareExtinctionContracts ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PoincareExtinctionContracts

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
