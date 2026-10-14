import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem binaryConnectedSumLaws_holds : binaryConnectedSumLaws.{u} :=
  binaryConnectedSumLaws_of_unit_assoc_comm_transport sphereUnitLaws_holds
    connectedSumCommutative_holds connectedSumAssociative_holds
    connectedSumOrientedTransport_holds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.binaryConnectedSumLaws_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.binaryConnectedSumLaws_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.binaryConnectedSumLaws_holds ``Submission.DifferentialGeometry.Topology.binaryConnectedSumLaws_holds

theorem connectedSumLaws_holds : connectedSumLaws.{u} :=
  connectedSumLaws_of_binaryConnectedSumLaws binaryConnectedSumLaws_holds

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumLaws_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumLaws_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumLaws_holds ``Submission.DifferentialGeometry.Topology.connectedSumLaws_holds

end DifferentialGeometry.Topology
