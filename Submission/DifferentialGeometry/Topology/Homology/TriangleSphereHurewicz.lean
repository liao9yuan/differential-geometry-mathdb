import Submission.DifferentialGeometry.Topology.Homology.SphereHurewiczPrecomposition
import Submission.DifferentialGeometry.Topology.Homology.TriangleSpherePairing
import Submission.DifferentialGeometry.Topology.Homology.SimplexBoundarySphereGenerator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def triangleSphereFundamentalClass :
    integralSingularHomology 2 (liftedHomotopySphere.{u} 1) :=
  integralSingularHomologyMap 2
    (liftedHomotopySphereMap 1 Simplex.triangleSphereCollapse)
      (simplexBoundarySphereClass.{u} 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.triangleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.triangleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.triangleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.triangleSphereFundamentalClass

theorem sphereHurewicz_integralSingularTriangleSphereClass
    (x : X) (σ : integralSingularSimplex 2 X) :
    sphereHurewicz 1 x triangleSphereFundamentalClass
      (integralSingularTriangleSphereClass x σ) =
        integralSingularCycleClass 1 X
          (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)) := by
  rw [triangleSphereFundamentalClass, sphereHurewicz_precompose,
    homotopyGroupSpherePrecompose_integralSingularTriangleSphereClass,
    sphereHurewicz_integralSingularConeSphereClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_integralSingularTriangleSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_integralSingularTriangleSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_integralSingularTriangleSphereClass ``Submission.DifferentialGeometry.Topology.sphereHurewicz_integralSingularTriangleSphereClass

theorem isSphereHomologyGenerator_triangleSphereFundamentalClass :
    IsSphereHomologyGenerator 1 triangleSphereFundamentalClass.{u} := by
  obtain ⟨e, he⟩ := Simplex.triangleSphereCollapse_homotopyEquiv
  have h := isSphereHomologyGenerator_liftedHomotopySphereMap 1 e
    isSphereHomologyGenerator_simplexBoundarySphereClass
  simpa only [he, triangleSphereFundamentalClass] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_triangleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_triangleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_triangleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_triangleSphereFundamentalClass

end DifferentialGeometry.Topology
