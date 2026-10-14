import Submission.DifferentialGeometry.Topology.Homology.TriangleBoundaryDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

def euclideanSimplexBoundaryDegree :
    integralSingularHomology 2 puncturedThreeSpace.{u} →ₗ[ℤ] ℤ :=
  puncturedPlaneDiagonalDegree.comp tetrahedronToTriangleHomology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree

theorem euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass :
    euclideanSimplexBoundaryDegree euclideanStandardSimplexBoundaryClass.{u} = 1 := by
  rw [euclideanSimplexBoundaryDegree, LinearMap.comp_apply,
    tetrahedronToTriangleHomology_euclideanStandardSimplexBoundaryClass,
    puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass

theorem euclideanStandardSimplexClass_generator :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) := by
  apply euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mpr
  apply (isSphereHomologyGenerator_iff_exists_functional 1 _).mpr
  let e := (integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2).trans
    (integralSingularHomologyHomotopyEquiv 2
      (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
  refine ⟨euclideanSimplexBoundaryDegree.comp e.symm.toLinearMap, ?_⟩
  change euclideanSimplexBoundaryDegree (e.symm (e euclideanStandardSimplexBoundaryClass.{u})) = 1
  rw [LinearEquiv.symm_apply_apply]
  exact euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator

end DifferentialGeometry.Topology.SimplexDegree
