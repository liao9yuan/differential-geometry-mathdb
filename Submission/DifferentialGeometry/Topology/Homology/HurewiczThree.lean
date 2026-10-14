import Submission.DifferentialGeometry.Topology.Homology.TetrahedronSphereChain
import Submission.DifferentialGeometry.Topology.Homology.TetrahedronSphereHomologyInverse
import Submission.DifferentialGeometry.Topology.Simplex.TetrahedronGenLoopRepresentation
import Submission.DifferentialGeometry.Topology.Homology.TetrahedronSphereIdentification
import Submission.DifferentialGeometry.Topology.Homology.SimplexBoundarySphereGenerator
import Submission.DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem sphereHurewicz_tetrahedronGenLoop
    (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin 4), g p = x) :
    sphereHurewicz 2 x tetrahedronSphereFundamentalClass
      (⟦Simplex.tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) =
        integralSingularCycleClass 2 X (integralSingularTetrahedronCycle g x hg) := by
  let a : HomotopyGroup (Fin 3) X x := ⟦Simplex.tetrahedronGenLoop g x hg⟧
  have h := sphereHurewicz_precompose 2 x Simplex.tetrahedronSphereCollapse
    (simplexBoundarySphereClass.{u} 2) a
  change sphereHurewicz 2 x tetrahedronSphereFundamentalClass a = _ at h
  rw [h]
  have he := Simplex.tetrahedronSphereMap_class_eq_precompose g x hg
  change (homotopyGroupFreeSphereEquiv 2 x).symm
    (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)) =
      homotopyGroupSpherePrecompose 2 x Simplex.tetrahedronSphereCollapse a at he
  rw [← he]
  change freeSphereHomologyImage 2 (simplexBoundarySphereClass.{u} 2)
    ((homotopyGroupFreeSphereEquiv 2 x) ((homotopyGroupFreeSphereEquiv 2 x).symm
      (ZerothHomotopy.mk (Simplex.tetrahedronSphereMap g x hg)))) = _
  rw [Equiv.apply_symm_apply, tetrahedronSphereMap_simplexBoundarySphereClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_tetrahedronGenLoop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_tetrahedronGenLoop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_tetrahedronGenLoop ``Submission.DifferentialGeometry.Topology.sphereHurewicz_tetrahedronGenLoop

theorem isSphereHomologyGenerator_tetrahedronSphereFundamentalClass :
    IsSphereHomologyGenerator 2 tetrahedronSphereFundamentalClass.{u} := by
  obtain ⟨e, he⟩ := Simplex.tetrahedronSphereCollapse_homotopyEquiv
  have h := isSphereHomologyGenerator_liftedHomotopySphereMap 2 e
    isSphereHomologyGenerator_simplexBoundarySphereClass_three
  simpa only [he, tetrahedronSphereFundamentalClass] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_tetrahedronSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_tetrahedronSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_tetrahedronSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_tetrahedronSphereFundamentalClass

variable (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)]

theorem integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz
    (a : HomotopyGroup (Fin 3) X x) :
    integralSingularTetrahedronSphereHomologyPairing x
      (sphereHurewicz 2 x tetrahedronSphereFundamentalClass a) = Additive.ofMul a := by
  obtain ⟨g, hg, rfl⟩ := Simplex.exists_tetrahedronGenLoop_class_eq a
  rw [sphereHurewicz_tetrahedronGenLoop, integralSingularTetrahedronSphereHomologyPairing_cycle,
    integralSingularTetrahedronCycle_val, integralSingularTetrahedronSpherePairing_simplex,
    integralSingularTetrahedronSphereClass_eq_tetrahedronGenLoop_of_boundary]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz ``Submission.DifferentialGeometry.Topology.integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz

theorem bijective_sphereHurewicz_tetrahedronSphereFundamentalClass :
    Function.Bijective (sphereHurewicz 2 x tetrahedronSphereFundamentalClass) := by
  constructor
  · intro a b h
    have h' := congrArg (integralSingularTetrahedronSphereHomologyPairing x) h
    rw [integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz,
      integralSingularTetrahedronSphereHomologyPairing_sphereHurewicz] at h'
    exact h'
  · intro y
    exact ⟨(integralSingularTetrahedronSphereHomologyPairing x y).toMul,
      sphereHurewicz_integralSingularTetrahedronSphereHomologyPairing x y⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_sphereHurewicz_tetrahedronSphereFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_sphereHurewicz_tetrahedronSphereFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_sphereHurewicz_tetrahedronSphereFundamentalClass ``Submission.DifferentialGeometry.Topology.bijective_sphereHurewicz_tetrahedronSphereFundamentalClass

theorem bijective_sphereHurewicz_three
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) := by
  apply (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 x c hc).mpr
  exact (bijective_sphereHurewicz_iff_bijective_integralLiftedSphereGenerator 2 x
    tetrahedronSphereFundamentalClass isSphereHomologyGenerator_tetrahedronSphereFundamentalClass).mp
      (bijective_sphereHurewicz_tetrahedronSphereFundamentalClass x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_sphereHurewicz_three then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_sphereHurewicz_three"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_sphereHurewicz_three ``Submission.DifferentialGeometry.Topology.bijective_sphereHurewicz_three

end DifferentialGeometry.Topology
