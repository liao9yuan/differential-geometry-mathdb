import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLaws
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLawsAssembly

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSum_orientedDiffeomorph_of_forall₂
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hf : List.Forall₂ (fun (M N : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        M.toClosedOrientedManifold N.toClosedOrientedManifold)) L K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumLaws connectedSumLaws_holds hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_orientedDiffeomorph_of_forall₂ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_orientedDiffeomorph_of_forall₂"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_orientedDiffeomorph_of_forall₂ ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_orientedDiffeomorph_of_forall₂

theorem finiteConnectedSum_append_orientedDiffeomorph
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (connectedSum (finiteConnectedSum L) (finiteConnectedSum K)).toClosedOrientedManifold) :=
  finiteConnectedSum_append_of_connectedSumLaws connectedSumLaws_holds L K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_append_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_append_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_append_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_append_orientedDiffeomorph

theorem finiteConnectedSum_perm_orientedDiffeomorph
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm K) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum L).toClosedOrientedManifold
      (finiteConnectedSum K).toClosedOrientedManifold) :=
  finiteConnectedSum_perm_of_connectedSumLaws connectedSumLaws_holds hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_perm_orientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_perm_orientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_perm_orientedDiffeomorph ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_perm_orientedDiffeomorph

theorem finiteConnectedSum_unique
    (f : List (ConnectedClosedOrientedManifold.{u} 3) → ConnectedClosedOrientedManifold.{u} 3)
    (h0 : f [] = standardThreeSphereLift.{u})
    (h1 : ∀ M : ConnectedClosedOrientedManifold.{u} 3, f [M] = M)
    (h2 : ∀ (M N : ConnectedClosedOrientedManifold.{u} 3)
      (L : List (ConnectedClosedOrientedManifold.{u} 3)),
      f (M :: N :: L) = connectedSum M (f (N :: L))) :
    f = finiteConnectedSum := by
  funext L
  induction L with
  | nil => exact h0
  | cons M t ih =>
      cases t with
      | nil => exact h1 M
      | cons N L =>
          rw [h2 M N L, ih]
          rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.finiteConnectedSum_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.finiteConnectedSum_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.finiteConnectedSum_unique ``Submission.DifferentialGeometry.Topology.finiteConnectedSum_unique

end DifferentialGeometry.Topology
