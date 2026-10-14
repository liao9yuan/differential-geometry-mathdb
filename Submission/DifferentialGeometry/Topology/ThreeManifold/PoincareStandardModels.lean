import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem isStandardFactor_sphereTwoTimesCircleLift :
    isStandardFactor sphereTwoTimesCircleLift :=
  isStandardFactor_of_isSphereTwoTimesCircleFactor
    isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isStandardFactor_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isStandardFactor_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isStandardFactor_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.isStandardFactor_sphereTwoTimesCircleLift

theorem isPoincareStandard_sphereTwoTimesCircleLift :
    isPoincareStandard sphereTwoTimesCircleLift.Carrier :=
  isPoincareStandard_of_standard_factor sphereTwoTimesCircleLift
    isStandardFactor_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.isPoincareStandard_sphereTwoTimesCircleLift

theorem isPoincareStandard_finiteConnectedSum_sphereTwoTimesCircleLift :
    isPoincareStandard (finiteConnectedSum [sphereTwoTimesCircleLift]).Carrier := by
  refine isPoincareStandard_finite_sum [sphereTwoTimesCircleLift] ?_
  intro F hF
  rw [List.mem_singleton] at hF
  subst hF
  exact isStandardFactor_sphereTwoTimesCircleLift

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isPoincareStandard_finiteConnectedSum_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isPoincareStandard_finiteConnectedSum_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isPoincareStandard_finiteConnectedSum_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.isPoincareStandard_finiteConnectedSum_sphereTwoTimesCircleLift

theorem nonempty_standardThreeSphereLift : Nonempty standardThreeSphereLift.Carrier :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_standardThreeSphereLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_standardThreeSphereLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_standardThreeSphereLift ``Submission.DifferentialGeometry.Topology.nonempty_standardThreeSphereLift

theorem nonempty_sphereTwoTimesCircleLift : Nonempty sphereTwoTimesCircleLift.Carrier :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_sphereTwoTimesCircleLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_sphereTwoTimesCircleLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_sphereTwoTimesCircleLift ``Submission.DifferentialGeometry.Topology.nonempty_sphereTwoTimesCircleLift

theorem nonempty_finiteConnectedSum
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (finiteConnectedSum L).Carrier :=
  inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_finiteConnectedSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_finiteConnectedSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_finiteConnectedSum ``Submission.DifferentialGeometry.Topology.nonempty_finiteConnectedSum

end DifferentialGeometry.Topology
