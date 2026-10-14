import Submission.DifferentialGeometry.Topology.Homology.ContractibleCoverSignFunctional
import Submission.DifferentialGeometry.Topology.Homology.TriangleRayComplement
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalVanishing
import Submission.DifferentialGeometry.Topology.Homology.TriangleBoundary

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

private instance _root_.Submission.DifferentialGeometry.Topology.SimplexDegree.instPathConnectedSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlane : PathConnectedSpace puncturedPlane.{u} :=
  puncturedSpace_pathConnected_of_finrank (liftedSphereSpace.{u} 0)
    (by rw [liftedSphereSpace_finrank]; norm_num)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.instPathConnectedSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlane
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.instPathConnectedSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlane target :: scope.openDecls } }

private instance _root_.Submission.DifferentialGeometry.Topology.SimplexDegree.instContractibleSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlanePuncturedPlanePositiveRayComplement : ContractibleSpace puncturedPlanePositiveRayComplement.{u} :=
  puncturedPlanePositiveRayComplement_contractibleSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.instContractibleSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlanePuncturedPlanePositiveRayComplement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.instContractibleSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlanePuncturedPlanePositiveRayComplement target :: scope.openDecls } }

private instance _root_.Submission.DifferentialGeometry.Topology.SimplexDegree.instContractibleSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlanePuncturedPlaneNegativeRayComplement : ContractibleSpace puncturedPlaneNegativeRayComplement.{u} :=
  puncturedPlaneNegativeRayComplement_contractibleSpace

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.instContractibleSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlanePuncturedPlaneNegativeRayComplement
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.instContractibleSpaceElemLiftedSphereSpaceOfNatNatPuncturedPlanePuncturedPlaneNegativeRayComplement target :: scope.openDecls } }

def puncturedPlaneDiagonalDegree : integralSingularHomology 1 puncturedPlane.{u} →ₗ[ℤ] ℤ :=
  integralHomologyOneCoverSignFunctional puncturedPlanePositiveRayComplement
    puncturedPlaneNegativeRayComplement isOpen_puncturedPlanePositiveRayComplement
    isOpen_puncturedPlaneNegativeRayComplement puncturedPlaneRayComplements_cover
    puncturedPlaneRayOverlapSign _root_.Bool.true

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree


theorem puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass :
    puncturedPlaneDiagonalDegree standardTriangleBoundaryClass.{u} = 1 := by
  change integralHomologyOneCoverSignFunctional puncturedPlanePositiveRayComplement
    puncturedPlaneNegativeRayComplement isOpen_puncturedPlanePositiveRayComplement
    isOpen_puncturedPlaneNegativeRayComplement puncturedPlaneRayComplements_cover
    puncturedPlaneRayOverlapSign _root_.Bool.true
      (integralHomologyClassOf 0 (integralChainHom 1 standardTriangleBoundaryChain) _) = 1
  rw [integralHomologyOneCoverSignFunctional_apply
    puncturedPlanePositiveRayComplement puncturedPlaneNegativeRayComplement
    isOpen_puncturedPlanePositiveRayComplement isOpen_puncturedPlaneNegativeRayComplement
    puncturedPlaneRayComplements_cover puncturedPlaneRayOverlapSign _root_.Bool.true
    (integralChainHom 1 standardTriangleBoundaryChain) _
    trianglePositiveEdgeChain triangleNegativeEdgeChain triangleEdgeChain_split
    (triangleOverlapVertex 0) (triangleOverlapVertex 1) triangleEdgeBoundaryChain_inclusion]
  simp [puncturedPlaneRayOverlapSign_apply, triangleOverlapVertex, standardTriangleVertex]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass

end DifferentialGeometry.Topology.SimplexDegree
