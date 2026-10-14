import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ContractiblePairOne

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The exact degree-one homology kernel for the original contractible cover -/

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- Retain the original kernel's integer action for the actual H0 inclusion map. -/
instance integralRelativeZeroKernelModule (A : Set X) :
    Module ℤ (LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A))) :=
  (LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A))).module

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeZeroKernelModule then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeZeroKernelModule"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeZeroKernelModule ``Submission.DifferentialGeometry.Topology.integralRelativeZeroKernelModule

/-- For a contractible original ambient space, the SAME connecting map
identifies relative H1 with the actual kernel of the ORIGINAL H0 inclusion map. -/
def integralRelativeConnectingZeroKernelEquiv [ContractibleSpace X] (A : Set X) :
    integralRelativeHomology 1 A ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A)) :=
  (LinearEquiv.ofInjective (integralRelativeConnecting 0 A)
    (integralRelativeConnecting_zero_injective A)).trans
      (LinearEquiv.ofEq _ _ ((LinearMap.exact_iff.mp (integralRelative_exact_subspace 0 A)).symm))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnectingZeroKernelEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnectingZeroKernelEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnectingZeroKernelEquiv ``Submission.DifferentialGeometry.Topology.integralRelativeConnectingZeroKernelEquiv

/-- A path-connected space covered by two actual contractible open sets
has ORIGINAL H1 identified with the actual kernel of the inclusion on H0
of the SAME intersection. This completes the low-degree cover computation. -/
def integralHomologyOneContractibleCoverEquiv [PathConnectedSpace X] (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = _root_.Set.univ) :
    integralSingularHomology 1 X ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion (subspaceIntersection A B))) :=
  ((integralAbsoluteToRelativeOneIsoOfContractible A).toLinearEquiv.trans
    (integralRelativeOpenExcisionIso 1 A B hA hB hcover).symm.toLinearEquiv).trans
      (integralRelativeConnectingZeroKernelEquiv (subspaceIntersection A B))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv ``Submission.DifferentialGeometry.Topology.integralHomologyOneContractibleCoverEquiv

end DifferentialGeometry.Topology
