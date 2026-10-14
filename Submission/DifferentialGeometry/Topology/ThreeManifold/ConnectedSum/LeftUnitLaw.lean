import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Commutative
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCapFillingIsometry

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

theorem nonempty_diffeomorph_connectedSum_sphere_left_unit
    (X : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty ((connectedSum standardThreeSphereLift.{u} X).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ X.toClosedOrientedManifold.Carrier) :=
  (nonempty_diffeomorph_connectedSum_comm standardThreeSphereLift.{u} X).elim fun e₁ =>
    (nonempty_diffeomorph_connectedSum_sphere_right_unit X).elim fun e₂ => ⟨e₁.trans e₂⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_left_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_left_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_left_unit ``Submission.DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_sphere_left_unit

end DifferentialGeometry.Topology
