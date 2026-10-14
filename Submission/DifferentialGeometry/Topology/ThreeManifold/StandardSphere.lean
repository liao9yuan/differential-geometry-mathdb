import Submission.DifferentialGeometry.Topology.Manifold.ClosedOriented
import Submission.DifferentialGeometry.Topology.Manifold.SphereOrientation
import Submission.DifferentialGeometry.Topology.Manifold.ULift
import Mathlib.Analysis.Normed.Module.Connected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Metric
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

def standardThreeSphere : ConnectedClosedOrientedManifold.{0} 3 where
  Carrier := _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  orientation := sphereOrientation 3 (by decide)
  connected := isConnected_iff_connectedSpace.mp
    (isConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 4)) (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.standardThreeSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.standardThreeSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.standardThreeSphere ``Submission.DifferentialGeometry.Topology.standardThreeSphere

@[simp]
theorem standardThreeSphere_carrier :
    standardThreeSphere.Carrier = _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.standardThreeSphere_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.standardThreeSphere_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.standardThreeSphere_carrier ``Submission.DifferentialGeometry.Topology.standardThreeSphere_carrier

def standardThreeSphereLift : ConnectedClosedOrientedManifold.{u} 3 :=
  ConnectedClosedOrientedManifold.ulift.{0, u} standardThreeSphere

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.standardThreeSphereLift

@[simp]
theorem standardThreeSphereLift_carrier :
    standardThreeSphereLift.{u}.Carrier =
      ULift.{u} (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.standardThreeSphereLift_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.standardThreeSphereLift_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.standardThreeSphereLift_carrier ``Submission.DifferentialGeometry.Topology.standardThreeSphereLift_carrier

def standardThreeSphereLiftDiffeomorph :
    standardThreeSphere.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ standardThreeSphereLift.{u}.Carrier :=
  ClosedOrientedManifold.uliftDiffeomorph standardThreeSphere.toClosedOrientedManifold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph ``Submission.DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph

theorem standardThreeSphereLiftDiffeomorph_preservesOrientation :
    standardThreeSphereLiftDiffeomorph.{u}.preservesOrientation
      standardThreeSphere.orientation standardThreeSphereLift.{u}.orientation :=
  ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation
    standardThreeSphere.toClosedOrientedManifold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph_preservesOrientation ``Submission.DifferentialGeometry.Topology.standardThreeSphereLiftDiffeomorph_preservesOrientation

end DifferentialGeometry.Topology
