import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosed
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws

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

theorem poincareStandardSumClosed_of_associative
    (hassoc : connectedSumAssociative.{u})
    (hup : ∀ F : ConnectedClosedOrientedManifold.{u} 3,
      isPoincareStandard F.Carrier → isOrientedPoincareStandard F.toClosedOrientedManifold) :
    poincareStandardSumClosed.{u} :=
  poincareStandardSumClosed_of_unit_commutative_associative
    sphereUnitLaws_holds connectedSumCommutative_holds hassoc hup

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.poincareStandardSumClosed_of_associative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.poincareStandardSumClosed_of_associative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.poincareStandardSumClosed_of_associative ``Submission.DifferentialGeometry.Topology.poincareStandardSumClosed_of_associative

end DifferentialGeometry.Topology
