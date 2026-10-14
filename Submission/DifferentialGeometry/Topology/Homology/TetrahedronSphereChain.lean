import Submission.DifferentialGeometry.Topology.Homology.SimplexSphereChain
import Submission.DifferentialGeometry.Topology.Homology.CycleClassMaps
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronSphere
import Submission.DifferentialGeometry.Topology.Homology.SphereHurewicz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap
open scoped _root_.Simplicial
namespace DifferentialGeometry.Topology
universe u
variable {X : Type u} [TopologicalSpace X]

theorem integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularChainMap
      ((Simplex.tetrahedronSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).f 3
      (simplexBoundarySphereChain.{u} 2) =
        integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g) :=
  integralSingularChainMap_simplexSphereMap_simplexBoundarySphereChain_of_even 2 (by decide) g x hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain ``Submission.DifferentialGeometry.Topology.integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain

theorem integralSimplexChain_three_boundary_eq_zero
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularChains X).d 3 2
      (integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g)) = 0 :=
  integralSimplexChain_boundary_eq_zero_of_even 2 (by decide) g x hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSimplexChain_three_boundary_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSimplexChain_three_boundary_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSimplexChain_three_boundary_eq_zero ``Submission.DifferentialGeometry.Topology.integralSimplexChain_three_boundary_eq_zero

def integralSingularTetrahedronCycle (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) : integralSingularCycles 2 X :=
  ⟨integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g),
    integralSimplexChain_three_boundary_eq_zero g x hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronCycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronCycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronCycle ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronCycle

theorem integralSingularTetrahedronCycle_val (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    (integralSingularTetrahedronCycle g x hg).val =
      integralSimplexChain 3 ((integralSingularSimplexEquiv 3 X).symm g) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronCycle_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronCycle_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronCycle_val ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronCycle_val

theorem tetrahedronSphereMap_simplexBoundarySphereClass
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
      (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)) =
        integralSingularCycleClass 2 X (integralSingularTetrahedronCycle g x hg) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass,
    integralSingularCycleClass_map]
  congr 1
  apply Subtype.ext
  rw [integralSingularCycleMap_val, integralSingularTetrahedronCycle_val]
  exact integralSingularChainMap_tetrahedronSphereMap_simplexBoundarySphereChain g x hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tetrahedronSphereMap_simplexBoundarySphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tetrahedronSphereMap_simplexBoundarySphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tetrahedronSphereMap_simplexBoundarySphereClass ``Submission.DifferentialGeometry.Topology.tetrahedronSphereMap_simplexBoundarySphereClass

end DifferentialGeometry.Topology
