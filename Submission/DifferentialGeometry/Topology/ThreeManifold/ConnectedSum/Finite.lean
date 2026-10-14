import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction
import Submission.DifferentialGeometry.Topology.ThreeManifold.StandardSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

def finiteConnectedSum : List (ConnectedClosedOrientedManifold.{u} 3) →
    ConnectedClosedOrientedManifold.{u} 3
  | [] => standardThreeSphereLift
  | [M] => M
  | M :: N :: L => connectedSum M (finiteConnectedSum (N :: L))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum ``Submission.DifferentialGeometry.Topology.finiteConnectedSum

@[simp]
theorem finiteConnectedSum_nil :
    finiteConnectedSum ([] : List (ConnectedClosedOrientedManifold.{u} 3)) =
      standardThreeSphereLift := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_nil then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_nil"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_nil ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_nil

@[simp]
theorem finiteConnectedSum_singleton (M : ConnectedClosedOrientedManifold.{u} 3) :
    finiteConnectedSum [M] = M := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_singleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_singleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_singleton ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_singleton

@[simp]
theorem finiteConnectedSum_cons_cons (M N : ConnectedClosedOrientedManifold.{u} 3)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    finiteConnectedSum (M :: N :: L) = connectedSum M (finiteConnectedSum (N :: L)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_cons_cons then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_cons_cons"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_cons_cons ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_cons_cons

end DifferentialGeometry.Topology
