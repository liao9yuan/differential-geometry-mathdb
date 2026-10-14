import Submission.DifferentialGeometry.Topology.Manifold.Sigma
import Submission.DifferentialGeometry.Topology.Manifold.Components
import Mathlib.Geometry.Manifold.Instances.Real

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Manifold
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology

universe u

section Union

variable {ι : Type u} [Fintype ι]

def closedOrientedUnion (M : ι → ClosedOrientedManifold.{u} 3) : ClosedOrientedManifold.{u} 3 where
  Carrier := Σ i, (M i).Carrier
  orientation := manifoldOrientationUnion (M := fun i => (M i).Carrier) (I := 𝓡 3)
    (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 by norm_num)
    (fun i => (M i).orientation)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedOrientedUnion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedOrientedUnion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedOrientedUnion ``Submission.DifferentialGeometry.Topology.closedOrientedUnion

theorem closedOrientedUnion_carrier (M : ι → ClosedOrientedManifold.{u} 3) :
    (closedOrientedUnion M).Carrier = (Σ i, (M i).Carrier) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedOrientedUnion_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedOrientedUnion_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedOrientedUnion_carrier ``Submission.DifferentialGeometry.Topology.closedOrientedUnion_carrier

theorem closedOrientedUnion_orientation (M : ι → ClosedOrientedManifold.{u} 3) (i : ι)
    (y : (M i).Carrier) :
    (closedOrientedUnion M).orientation.orientation (⟨i, y⟩ : Σ j, (M j).Carrier) =
      (M i).orientation.orientation y := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.closedOrientedUnion_orientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.closedOrientedUnion_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.closedOrientedUnion_orientation ``Submission.DifferentialGeometry.Topology.closedOrientedUnion_orientation


end Union

end DifferentialGeometry.Topology
