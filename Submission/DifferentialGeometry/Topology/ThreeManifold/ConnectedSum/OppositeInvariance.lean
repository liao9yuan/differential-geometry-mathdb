import Submission.DifferentialGeometry.Topology.Manifold.DiffeomorphOrientationDichotomy
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected

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

def connectedSumOppositeInvariance : Prop :=
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty ((connectedSum X.opposite Y).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum X Y).toClosedOrientedManifold.Carrier)) ∧
  (∀ X Y : ConnectedClosedOrientedManifold.{u} 3,
    Nonempty ((connectedSum X Y.opposite).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      (connectedSum X Y).toClosedOrientedManifold.Carrier))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOppositeInvariance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOppositeInvariance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOppositeInvariance ``Submission.DifferentialGeometry.Topology.connectedSumOppositeInvariance

theorem connectedSumOppositeInvariance_of_transport
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
    connectedSumOppositeInvariance.{u} :=
  ⟨fun X Y => htransportL X.opposite X Y ⟨Diffeomorph.refl (𝓡 3) X.Carrier ∞⟩,
    fun X Y => htransportR X Y.opposite Y ⟨Diffeomorph.refl (𝓡 3) Y.Carrier ∞⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSumOppositeInvariance_of_transport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSumOppositeInvariance_of_transport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSumOppositeInvariance_of_transport ``Submission.DifferentialGeometry.Topology.connectedSumOppositeInvariance_of_transport

theorem connectedSum_transport_left_of_oppositeInvariance
    (h : connectedSumOppositeInvariance.{u}) :
    ∀ X X' Y : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (X.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        X'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X' Y).toClosedOrientedManifold.Carrier) := by
  intro X X' Y hX
  obtain ⟨Φ⟩ := hX
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite
    Φ X.orientation X'.orientation with hΦ | hΦ
  · exact connectedSum_transport_left_holds X X' Y Φ hΦ
  · obtain ⟨f⟩ := connectedSum_transport_left_holds X X'.opposite Y Φ hΦ
    obtain ⟨g⟩ := h.1 X' Y
    exact ⟨f.trans g⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_transport_left_of_oppositeInvariance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_transport_left_of_oppositeInvariance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_transport_left_of_oppositeInvariance ``Submission.DifferentialGeometry.Topology.connectedSum_transport_left_of_oppositeInvariance

theorem connectedSum_transport_right_of_oppositeInvariance
    (h : connectedSumOppositeInvariance.{u}) :
    ∀ X Y Y' : ConnectedClosedOrientedManifold.{u} 3,
      Nonempty (Y.toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        Y'.toClosedOrientedManifold.Carrier) →
      Nonempty ((connectedSum X Y).toClosedOrientedManifold.Carrier
        ≃ₘ⟮𝓡 3, 𝓡 3⟯ (connectedSum X Y').toClosedOrientedManifold.Carrier) := by
  intro X Y Y' hY
  obtain ⟨Ψ⟩ := hY
  rcases Diffeomorph.preservesOrientation_or_preservesOrientation_opposite
    Ψ Y.orientation Y'.orientation with hΨ | hΨ
  · exact connectedSum_transport_right_holds X Y Y' Ψ hΨ
  · obtain ⟨f⟩ := connectedSum_transport_right_holds X Y Y'.opposite Ψ hΨ
    obtain ⟨g⟩ := h.2 X Y'
    exact ⟨f.trans g⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.connectedSum_transport_right_of_oppositeInvariance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.connectedSum_transport_right_of_oppositeInvariance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.connectedSum_transport_right_of_oppositeInvariance ``Submission.DifferentialGeometry.Topology.connectedSum_transport_right_of_oppositeInvariance

end DifferentialGeometry.Topology
