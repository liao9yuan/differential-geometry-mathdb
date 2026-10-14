import Submission.DifferentialGeometry.Topology.Manifold.ComponentDiffeomorph
import Submission.DifferentialGeometry.Topology.ThreeManifold.PoincareStandard

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u
variable {M N : ClosedOrientedManifold.{u} 3}

theorem componentwise_isPoincareStandard_iff_of_diffeomorph
    (e : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ N.Carrier) :
    (∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier) ↔
      ∀ C : ConnectedComponents N.Carrier, isPoincareStandard (N.component C).Carrier := by
  constructor
  · intro h C
    exact isPoincareStandard_of_diffeomorph (diffeomorphComponent e.symm C) (h _)
  · intro h C
    exact isPoincareStandard_of_diffeomorph (diffeomorphComponent e C) (h _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwise_isPoincareStandard_iff_of_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.componentwise_isPoincareStandard_iff_of_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.componentwise_isPoincareStandard_iff_of_diffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.componentwise_isPoincareStandard_iff_of_diffeomorph

end DifferentialGeometry.Topology.ClosedOrientedManifold
