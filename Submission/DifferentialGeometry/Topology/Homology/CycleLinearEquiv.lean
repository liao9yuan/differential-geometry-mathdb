import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cochains
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Cycles

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

abbrev integralSingularCocycles (n : ℕ) (X : Type u) [TopologicalSpace X] :=
  LinearMap.ker ((integralSingularCochains X).d (n + 1) (n + 2)).hom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCocycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCocycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCocycles ``Submission.DifferentialGeometry.Topology.integralSingularCocycles

def integralSingularCoboundaryToCycles (n : ℕ) (X : Type u) [TopologicalSpace X] :
    integralSingularCochain n X →ₗ[ℤ] integralSingularCocycles n X :=
  ((integralSingularCochains X).sc' n (n + 1) (n + 2)).moduleCatToCycles

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCoboundaryToCycles then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCoboundaryToCycles"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCoboundaryToCycles ``Submission.DifferentialGeometry.Topology.integralSingularCoboundaryToCycles

def integralSingularHomologyCycleLinearEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ↑(integralSingularHomology (n + 1) X) ≃ₗ[ℤ]
      (integralSingularCycles n X ⧸ LinearMap.range (integralSingularBoundaryToCycles n X)) :=
  AddEquiv.toIntLinearEquiv (integralSingularHomologyCycleEquiv n X)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyCycleLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyCycleLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyCycleLinearEquiv ``Submission.DifferentialGeometry.Topology.integralSingularHomologyCycleLinearEquiv

def integralSingularCohomologyCycleLinearEquiv (n : ℕ) (X : Type u) [TopologicalSpace X] :
    ↑(integralSingularCohomology (n + 1) X) ≃ₗ[ℤ]
      (integralSingularCocycles n X ⧸
        LinearMap.range (integralSingularCoboundaryToCycles n X)) :=
  let iso := ShortComplex.homologyMapIso ((integralSingularCochains X).isoSc'
    n (n + 1) (n + 2) (by simp) (by simp)) ≪≫
    ((integralSingularCochains X).sc' n (n + 1) (n + 2)).moduleCatHomologyIso
  iso.toLinearEquiv.toAddEquiv.toIntLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCohomologyCycleLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCohomologyCycleLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCohomologyCycleLinearEquiv ``Submission.DifferentialGeometry.Topology.integralSingularCohomologyCycleLinearEquiv

end DifferentialGeometry.Topology
