import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OppositeInvariance
import Submission.DifferentialGeometry.Topology.Manifold.SphereLinearIsometry

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u

def connectedSumOppositeSelfInvariance : Prop :=
  ∀ X : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty ((connectedSum X.opposite X).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X X).toClosedOrientedManifold.Carrier)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance ``Submission.DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance

theorem connectedSumOppositeSelfInvariance_of_oppositeInvariance
    (h : connectedSumOppositeInvariance.{u}) : connectedSumOppositeSelfInvariance.{u} :=
  fun X => h.1 X X

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_oppositeInvariance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_oppositeInvariance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_oppositeInvariance ``Submission.DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_oppositeInvariance

theorem connectedSumOppositeSelfInvariance_of_transport
    (htransportL : ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X' Y).toClosedOrientedManifold.Carrier))
    (htransportR : ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X Y').toClosedOrientedManifold.Carrier)) :
    connectedSumOppositeSelfInvariance.{u} :=
  connectedSumOppositeSelfInvariance_of_oppositeInvariance
    (connectedSumOppositeInvariance_of_transport htransportL htransportR)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_transport ``Submission.DifferentialGeometry.Topology.connectedSumOppositeSelfInvariance_of_transport

theorem nonempty_diffeomorph_connectedSum_opposite_left_of_orientedDiffeomorph
    (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (Φ : ClosedOrientedManifold.OrientedDiffeomorph
      X.opposite.toClosedOrientedManifold X.toClosedOrientedManifold) :
    Nonempty ((connectedSum X.opposite Y).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X Y).toClosedOrientedManifold.Carrier) :=
  connectedSum_transport_left_holds X.opposite X Y Φ.1 Φ.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_left_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_left_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_left_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_left_of_orientedDiffeomorph

theorem nonempty_diffeomorph_connectedSum_opposite_right_of_orientedDiffeomorph
    (X Y : ConnectedClosedOrientedManifold.{u} 3)
    (Φ : ClosedOrientedManifold.OrientedDiffeomorph
      Y.opposite.toClosedOrientedManifold Y.toClosedOrientedManifold) :
    Nonempty ((connectedSum X Y.opposite).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X Y).toClosedOrientedManifold.Carrier) :=
  connectedSum_transport_right_holds X Y.opposite Y Φ.1 Φ.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_right_of_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_right_of_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_right_of_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_right_of_orientedDiffeomorph

theorem nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph
    (Y : ConnectedClosedOrientedManifold.{u} 3)
    (h : Nonempty (Y.toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯
      standardThreeSphereLift.{u}.toClosedOrientedManifold.Carrier)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph Y.toClosedOrientedManifold
      standardThreeSphereLift.{u}.toClosedOrientedManifold) := by
  obtain ⟨Φ⟩ := h
  by_cases hΦ : Φ.preservesOrientation Y.orientation standardThreeSphereLift.{u}.orientation
  · exact ⟨Φ, hΦ⟩
  · rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite Φ Y.orientation
      standardThreeSphereLift.{u}.orientation with h' | h'
    · exact absurd h' hΦ
    · obtain ⟨τ⟩ := standardThreeSphereLift_orientationReversing_diffeomorph.{u}
      exact ⟨Φ.trans τ.1, Diffeomorph.preservesOrientation_trans h' τ.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph ``Submission.DifferentialGeometry.Topology.nonempty_orientedDiffeomorph_standardThreeSphere_of_diffeomorph

theorem nonempty_diffeomorph_connectedSum_opposite_sphere_left
    (Y : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty ((connectedSum standardThreeSphereLift.{u}.opposite Y).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum standardThreeSphereLift.{u} Y).toClosedOrientedManifold.Carrier) := by
  obtain ⟨Φ⟩ := standardThreeSphereLift_orientationReversing_diffeomorph.{u}
  exact nonempty_diffeomorph_connectedSum_opposite_left_of_orientedDiffeomorph
    standardThreeSphereLift.{u} Y Φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_left ``Submission.DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_left

theorem nonempty_diffeomorph_connectedSum_opposite_sphere_right
    (X : ConnectedClosedOrientedManifold.{u} 3) :
    Nonempty ((connectedSum X standardThreeSphereLift.{u}.opposite).toClosedOrientedManifold.Carrier
      ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum X standardThreeSphereLift.{u}).toClosedOrientedManifold.Carrier) := by
  obtain ⟨Φ⟩ := standardThreeSphereLift_orientationReversing_diffeomorph.{u}
  exact nonempty_diffeomorph_connectedSum_opposite_right_of_orientedDiffeomorph
    X standardThreeSphereLift.{u} Φ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_right ``Submission.DifferentialGeometry.Topology.nonempty_diffeomorph_connectedSum_opposite_sphere_right

end DifferentialGeometry.Topology
