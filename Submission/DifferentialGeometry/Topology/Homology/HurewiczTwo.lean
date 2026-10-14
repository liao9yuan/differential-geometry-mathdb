import Submission.DifferentialGeometry.Topology.Homology.SphereNullity
import Submission.DifferentialGeometry.Topology.Homology.TriangleSphereHomologyInverse
import Submission.DifferentialGeometry.Topology.Homology.HurewiczNullhomotopyCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem injective_sphereHurewicz_simplexBoundarySphereClass (x : X) :
    Function.Injective (sphereHurewicz 1 x (simplexBoundarySphereClass.{u} 1)) := by
  apply (injective_sphereHurewicz_iff_forall_eq_one_of_additive 1 x (simplexBoundarySphereClass 1)
    (fun a b => sphereHurewicz_two_mul x (simplexBoundarySphereClass 1) a b)).mpr
  apply (forall_sphereHurewicz_eq_zero_iff_forall_freeSphereHomologyImage_eq_zero 1 x
    (simplexBoundarySphereClass 1)).mpr
  intro f hf
  exact (zerothHomotopy_mk_eq_const_iff_nullhomotopic 1 x f).mpr
    (nullhomotopic_of_freeSphereHomologyImage_simplexBoundary_eq_zero x f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_sphereHurewicz_simplexBoundarySphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_sphereHurewicz_simplexBoundarySphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_sphereHurewicz_simplexBoundarySphereClass ``Submission.DifferentialGeometry.Topology.injective_sphereHurewicz_simplexBoundarySphereClass

theorem injective_sphereHurewicz_triangleSphereFundamentalClass (x : X) :
    Function.Injective (sphereHurewicz 1 x triangleSphereFundamentalClass) := by
  intro a b hab
  apply (Simplex.homotopyGroupSpherePrecompose_triangleSphereCollapse_bijective x).injective
  apply injective_sphereHurewicz_simplexBoundarySphereClass x
  simpa only [triangleSphereFundamentalClass, sphereHurewicz_precompose] using hab

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.injective_sphereHurewicz_triangleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.injective_sphereHurewicz_triangleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.injective_sphereHurewicz_triangleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.injective_sphereHurewicz_triangleSphereFundamentalClass

theorem bijective_sphereHurewicz_triangleSphereFundamentalClass (x : X) :
    Function.Bijective (sphereHurewicz 1 x triangleSphereFundamentalClass) := by
  refine ⟨injective_sphereHurewicz_triangleSphereFundamentalClass x, ?_⟩
  intro y
  exact ⟨(integralSingularTriangleSphereHomologyPairing x y).toMul,
    sphereHurewicz_integralSingularTriangleSphereHomologyPairing x y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_sphereHurewicz_triangleSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_sphereHurewicz_triangleSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_sphereHurewicz_triangleSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.bijective_sphereHurewicz_triangleSphereFundamentalClass

theorem bijective_sphereHurewicz_two (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Function.Bijective (sphereHurewicz 1 x c) := by
  apply (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 1 x c hc).mpr
  exact (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 1 x
    triangleSphereFundamentalClass isSphereHomologyGenerator_triangleSphereFundamentalClass).mp
      (bijective_sphereHurewicz_triangleSphereFundamentalClass x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_sphereHurewicz_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_sphereHurewicz_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_sphereHurewicz_two ``Submission.DifferentialGeometry.Topology.bijective_sphereHurewicz_two

theorem integralSingularTriangleSphereHomologyPairing_sphereHurewicz
    (x : X) (a : HomotopyGroup (Fin 2) X x) :
    integralSingularTriangleSphereHomologyPairing x
      (sphereHurewicz 1 x triangleSphereFundamentalClass a) = Additive.ofMul a := by
  apply Additive.toMul.injective
  apply injective_sphereHurewicz_triangleSphereFundamentalClass x
  exact sphereHurewicz_integralSingularTriangleSphereHomologyPairing x _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTriangleSphereHomologyPairing_sphereHurewicz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTriangleSphereHomologyPairing_sphereHurewicz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTriangleSphereHomologyPairing_sphereHurewicz ``Submission.DifferentialGeometry.Topology.integralSingularTriangleSphereHomologyPairing_sphereHurewicz

end DifferentialGeometry.Topology
