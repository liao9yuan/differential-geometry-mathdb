import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SumLaws

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem connectedSum_sphere_left (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum standardThreeSphereLift.{u} M).toClosedOrientedManifold
      M.toClosedOrientedManifold) :=
  connectedSum_sphere_left_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_sphere_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_sphere_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_sphere_left ``Submission.DifferentialGeometry.Topology.connectedSum_sphere_left

theorem connectedSum_sphere_right (M : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M standardThreeSphereLift.{u}).toClosedOrientedManifold
      M.toClosedOrientedManifold) :=
  connectedSum_sphere_right_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds M

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_sphere_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_sphere_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_sphere_right ``Submission.DifferentialGeometry.Topology.connectedSum_sphere_right

theorem finiteConnectedSum_append (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) :=
  finiteConnectedSum_append_of_connectedSumLaws connectedSumLaws_holds L K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_append then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_append"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_append ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_append

theorem finiteConnectedSum_congr {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumLaws connectedSumLaws_holds hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_congr ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_congr

theorem finiteConnectedSum_opposite (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).opposite.toClosedOrientedManifold
      (finiteConnectedSum
        (L.map ConnectedClosedOrientedManifold.opposite)).toClosedOrientedManifold) :=
  finiteConnectedSum_opposite_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds
    connectedSumOpposite_holds L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_opposite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_opposite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_opposite ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_opposite

end DifferentialGeometry.Topology
