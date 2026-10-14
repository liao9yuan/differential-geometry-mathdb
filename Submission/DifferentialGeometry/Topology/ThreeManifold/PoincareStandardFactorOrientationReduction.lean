import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeSumOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardFactorOrientation

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

theorem poincareStandardOrientationRefinement_of_factorOrientationClosure
    (hstd : factorOrientationClosure.{u}) : poincareStandardOrientationRefinement.{u} :=
  poincareStandardOrientationRefinement_of_connectedSumOpposite_and_factorOrientationClosure
    connectedSumOpposite_holds hstd

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_factorOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_factorOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_factorOrientationClosure ``Submission.DifferentialGeometry.Topology.poincareStandardOrientationRefinement_of_factorOrientationClosure

theorem poincareStandardSumClosed_of_factorOrientationClosure
    (hstd : factorOrientationClosure.{u}) : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_orientationRefinement
    (poincareStandardOrientationRefinement_of_factorOrientationClosure hstd)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_of_factorOrientationClosure then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_of_factorOrientationClosure"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_of_factorOrientationClosure ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_of_factorOrientationClosure

end DifferentialGeometry.Topology
