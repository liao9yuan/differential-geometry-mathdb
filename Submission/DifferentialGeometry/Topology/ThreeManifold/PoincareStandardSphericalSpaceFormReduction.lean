import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientationReduction
import Submission.DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleOrientationClosure

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

theorem factorOrientationClosure_of_sphericalSpaceFormOrientationClosure
    (hform : sphericalSpaceFormOrientationClosure) : factorOrientationClosure.{u} :=
  factorOrientationClosure_of_sphereTwoTimesCircle_and_sphericalSpaceForm
    sphereTwoTimesCircleOrientationClosure_holds hform

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.factorOrientationClosure_of_sphericalSpaceFormOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.factorOrientationClosure_of_sphericalSpaceFormOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.factorOrientationClosure_of_sphericalSpaceFormOrientationClosure ``Submission.DifferentialGeometry.Topology.factorOrientationClosure_of_sphericalSpaceFormOrientationClosure

theorem poincareStandardOrientationRefinement_of_sphericalSpaceFormOrientationClosure
    (hform : sphericalSpaceFormOrientationClosure) : poincareStandardOrientationRefinement.{u} :=
  poincareStandardOrientationRefinement_of_factorOrientationClosure
    (factorOrientationClosure_of_sphericalSpaceFormOrientationClosure hform)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_sphericalSpaceFormOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_sphericalSpaceFormOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_sphericalSpaceFormOrientationClosure ``Submission.DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_sphericalSpaceFormOrientationClosure

theorem poincareStandardSumClosed_of_sphericalSpaceFormOrientationClosure
    (hform : sphericalSpaceFormOrientationClosure) : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_factorOrientationClosure
    (factorOrientationClosure_of_sphericalSpaceFormOrientationClosure hform)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_of_sphericalSpaceFormOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_of_sphericalSpaceFormOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_of_sphericalSpaceFormOrientationClosure ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_of_sphericalSpaceFormOrientationClosure

end DifferentialGeometry.Topology
