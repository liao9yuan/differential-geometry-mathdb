import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssociativeFlattening
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosedAssociative

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

def poincareStandardOrientationRefinement : Prop :=
  ∀ F : ConnectedClosedOrientedManifold.{u} 3,
    isPoincareStandard F.Carrier → isOrientedPoincareStandard F.toClosedOrientedManifold

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardOrientationRefinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardOrientationRefinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardOrientationRefinement ``Submission.DifferentialGeometry.Topology.poincareStandardOrientationRefinement

theorem poincareStandardSumClosed_of_orientationRefinement
    (h : poincareStandardOrientationRefinement.{u}) : poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_associative connectedSumAssociative_holds h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_of_orientationRefinement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_of_orientationRefinement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_of_orientationRefinement ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_of_orientationRefinement

end DifferentialGeometry.Topology
