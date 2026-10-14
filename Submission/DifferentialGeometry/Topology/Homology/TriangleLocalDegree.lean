import Submission.DifferentialGeometry.Topology.Homology.Relative.Basic
import Submission.DifferentialGeometry.Topology.Homology.TriangleBoundaryDegree
import Submission.DifferentialGeometry.Topology.Homology.SquareBoundaryDegree

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial _root_.Topology

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

private theorem standardTriangleBoundaryChain_inclusion_hom :
    integralChainHom 1 standardTriangleBoundaryChain.{u} ≫
      (integralSingularChainMap (singularSubspaceInclusion puncturedPlane.{u})).f 1 =
        integralChainHom 2 standardTriangleChain.{u} ≫
          (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 := by
  rw [integralChainHom_comp_map, standardTriangleBoundaryChain_inclusion, integralChainHom_d]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTriangleBoundaryChain_inclusion_hom
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.standardTriangleBoundaryChain_inclusion_hom target :: scope.openDecls } }

def standardTriangleRelativeChain :
    integralSingularCoefficients ⟶ (integralRelativeChains puncturedPlane.{u}).X 2 :=
  integralChainHom 2 standardTriangleChain ≫ (integralRelativeProjection puncturedPlane).f 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain

theorem standardTriangleRelativeChain_boundary :
    standardTriangleRelativeChain.{u} ≫ (integralRelativeChains puncturedPlane).d 2 1 = 0 :=
  integralRelativeChain_projection_boundary 0 puncturedPlane
    (integralChainHom 2 standardTriangleChain) (integralChainHom 1 standardTriangleBoundaryChain)
    standardTriangleBoundaryChain_inclusion_hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain_boundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTriangleRelativeChain_boundary

def standardTriangleLocalClass : integralLocalHomology 2 (0 : liftedSphereSpace.{u} 0) :=
  integralRelativeClassOf 1 puncturedPlane standardTriangleRelativeChain
    standardTriangleRelativeChain_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalClass

theorem integralRelativeConnecting_standardTriangleLocalClass :
    integralRelativeConnecting 1 puncturedPlane standardTriangleLocalClass.{u} =
      standardTriangleBoundaryClass :=
  integralRelativeConnecting_liftCycles_apply 0 puncturedPlane
    (integralChainHom 2 standardTriangleChain) standardTriangleRelativeChain_boundary
    (integralChainHom 1 standardTriangleBoundaryChain)
    (by rw [integralChainHom_d 0 standardTriangleBoundaryChain,
      standardTriangleBoundaryChain_boundary, integralChainHom_zero])
    standardTriangleBoundaryChain_inclusion_hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_standardTriangleLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_standardTriangleLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_standardTriangleLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_standardTriangleLocalClass

def standardTriangleLocalDegree :
    integralLocalHomology 2 (0 : liftedSphereSpace.{u} 0) →ₗ[ℤ] ℤ :=
  puncturedPlaneDiagonalDegree.comp (integralRelativeConnecting 1 puncturedPlane)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree

theorem standardTriangleLocalDegree_standardTriangleLocalClass :
    standardTriangleLocalDegree standardTriangleLocalClass.{u} = 1 := by
  rw [standardTriangleLocalDegree, LinearMap.comp_apply,
    integralRelativeConnecting_standardTriangleLocalClass,
    puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree_standardTriangleLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree_standardTriangleLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree_standardTriangleLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTriangleLocalDegree_standardTriangleLocalClass

end DifferentialGeometry.Topology.SimplexDegree
