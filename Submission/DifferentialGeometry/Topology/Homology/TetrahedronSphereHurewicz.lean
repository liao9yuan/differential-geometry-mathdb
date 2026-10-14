import Submission.DifferentialGeometry.Topology.Homology.SphereHurewiczPrecomposition
import Submission.DifferentialGeometry.Topology.Homology.TetrahedronSpherePairing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def tetrahedronSphereFundamentalClass :
    integralSingularHomology 3 (liftedHomotopySphere.{u} 2) :=
  integralSingularHomologyMap 3
    (liftedHomotopySphereMap 2 Simplex.tetrahedronSphereCollapse)
      (simplexBoundarySphereClass.{u} 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tetrahedronSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tetrahedronSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tetrahedronSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.tetrahedronSphereFundamentalClass

theorem sphereHurewicz_integralSingularTetrahedronSphereClass
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] (σ : integralSingularSimplex 3 X) :
    sphereHurewicz 2 x tetrahedronSphereFundamentalClass
      (integralSingularTetrahedronSphereClass x σ) =
        integralSingularCycleClass 2 X
          (integralSingularThreeCycleProjection x (integralSimplexChain 3 σ)) := by
  rw [tetrahedronSphereFundamentalClass, sphereHurewicz_precompose,
    homotopyGroupSpherePrecompose_integralSingularTetrahedronSphereClass,
    sphereHurewicz_integralSingularConeThreeSphereClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_integralSingularTetrahedronSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_integralSingularTetrahedronSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_integralSingularTetrahedronSphereClass ``Submission.DifferentialGeometry.Topology.sphereHurewicz_integralSingularTetrahedronSphereClass

end DifferentialGeometry.Topology
