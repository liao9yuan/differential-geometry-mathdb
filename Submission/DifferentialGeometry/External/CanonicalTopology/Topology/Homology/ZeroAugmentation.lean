import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TotallyDisconnectedZero
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ConnectedZeroHomology
import Mathlib.LinearAlgebra.Finsupp.Pi

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The normalized augmentation of actual integral H0 -/

noncomputable section

open _root_.CategoryTheory _root_.ContinuousMap

universe u

namespace DifferentialGeometry.Topology

/-- Original H0 of the one-point space, normalized by its actual vertex. -/
def integralPointZeroEquiv :
    integralSingularHomology 0 PUnit.{u + 1} ≃ₗ[ℤ] ℤ :=
  integralTotallyDisconnectedZeroEquiv.trans (Finsupp.uniqueLinearEquiv ℤ ℤ PUnit.unit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralPointZeroEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralPointZeroEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralPointZeroEquiv ``Submission.DifferentialGeometry.Topology.integralPointZeroEquiv

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual H0 map to a point, in normalized integral coordinates. -/
def integralZeroAugmentation : integralSingularHomology 0 X →ₗ[ℤ] ℤ :=
  integralPointZeroEquiv.toLinearMap.comp
    (integralSingularHomologyMap 0 (ContinuousMap.const X PUnit.unit))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroAugmentation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroAugmentation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroAugmentation ``Submission.DifferentialGeometry.Topology.integralZeroAugmentation

/-- Every original vertex class has augmentation one. -/
theorem integralZeroAugmentation_vertex (x : X) :
    integralZeroAugmentation (integralZeroChainClass (integralVertexChain x)) = 1 := by
  change integralPointZeroEquiv (integralSingularHomologyMap 0 (.const X PUnit.unit)
    (integralZeroChainClass (integralVertexChain x))) = _
  rw [integralZeroChainClass_map, integralVertexChain_map]
  change Finsupp.uniqueLinearEquiv ℤ ℤ PUnit.unit
    (integralTotallyDisconnectedZeroEquiv (integralZeroChainClass
      (integralVertexChain PUnit.unit))) = _
  rw [integralTotallyDisconnectedZeroEquiv_vertex]
  simp [Finsupp.uniqueLinearEquiv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroAugmentation_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroAugmentation_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroAugmentation_vertex ``Submission.DifferentialGeometry.Topology.integralZeroAugmentation_vertex

/-- The augmentation commutes with every original continuous map. -/
theorem integralZeroAugmentation_natural (f : C(X, Y)) :
    integralZeroAugmentation.comp (integralSingularHomologyMap 0 f) =
      integralZeroAugmentation := by
  unfold integralZeroAugmentation
  rw [LinearMap.comp_assoc, ← integralSingularHomologyMap_comp]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralZeroAugmentation_natural then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralZeroAugmentation_natural"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralZeroAugmentation_natural ``Submission.DifferentialGeometry.Topology.integralZeroAugmentation_natural

/-- On a path-connected space the SAME normalized augmentation is an
isomorphism, as proved using actual paths and the actual map to a point. -/
def integralConnectedZeroAugmentationEquiv [PathConnectedSpace X] :
    integralSingularHomology 0 X ≃ₗ[ℤ] ℤ :=
  (integralSingularHomologyZeroMapEquiv (ContinuousMap.const X PUnit.unit)).trans
    integralPointZeroEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv ``Submission.DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv

/-- This equivalence uses the SAME augmentation, not an arbitrary H0 basis. -/
theorem integralConnectedZeroAugmentationEquiv_toLinearMap [PathConnectedSpace X] :
    (integralConnectedZeroAugmentationEquiv (X := X)).toLinearMap = integralZeroAugmentation := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv_toLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv_toLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv_toLinearMap ``Submission.DifferentialGeometry.Topology.integralConnectedZeroAugmentationEquiv_toLinearMap

end DifferentialGeometry.Topology
