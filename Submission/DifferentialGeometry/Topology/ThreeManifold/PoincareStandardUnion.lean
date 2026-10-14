import Submission.DifferentialGeometry.Topology.Manifold.DisjointUnionComponent
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandardOriented

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology
universe u
variable {ι : Type u} [Fintype ι] (M : ι → ClosedOrientedManifold.{u} 3)

theorem componentwise_isOrientedPoincareStandard_closedOrientedUnion
    (hM : ∀ i, ∀ C : ConnectedComponents (M i).Carrier,
      isOrientedPoincareStandard ((M i).component C).toClosedOrientedManifold)
    (C : ConnectedComponents (closedOrientedUnion M).Carrier) :
    isOrientedPoincareStandard ((closedOrientedUnion M).component C).toClosedOrientedManifold := by
  obtain ⟨⟨i, x⟩, rfl⟩ := ConnectedComponents.surjective_coe C
  exact isOrientedPoincareStandard_of_orientedDiffeomorph
    (closedOrientedUnionComponent M i x).symm (hM i (ConnectedComponents.mk x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.componentwise_isOrientedPoincareStandard_closedOrientedUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.componentwise_isOrientedPoincareStandard_closedOrientedUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.componentwise_isOrientedPoincareStandard_closedOrientedUnion ``Submission.DifferentialGeometry.Topology.componentwise_isOrientedPoincareStandard_closedOrientedUnion

end DifferentialGeometry.Topology
