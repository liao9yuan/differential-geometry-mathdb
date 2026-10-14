import Submission.DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereHomologyVanishing
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Metric _root_.Module

universe u

namespace DifferentialGeometry.Topology

theorem not_isSphereHomologyGenerator_zero (n : ℕ) :
    ¬ IsSphereHomologyGenerator n
      (0 : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)) := by
  intro h
  obtain ⟨φ, hφ⟩ := (isSphereHomologyGenerator_iff_exists_functional n 0).mp h
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (by rw [map_zero] at hφ; exact hφ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_isSphereHomologyGenerator_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_isSphereHomologyGenerator_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_isSphereHomologyGenerator_zero ``Submission.DifferentialGeometry.Topology.not_isSphereHomologyGenerator_zero

theorem exists_functional_integralLiftedSphereGenerator_eq_one (n : ℕ) :
    ∃ φ : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) →ₗ[ℤ] ℤ,
      φ (integralLiftedSphereGenerator.{u} n) = 1 :=
  ⟨(integralLiftedSphereTopEquiv n).toLinearMap, integralLiftedSphereGenerator_coordinate n⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_functional_integralLiftedSphereGenerator_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_functional_integralLiftedSphereGenerator_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_functional_integralLiftedSphereGenerator_eq_one ``Submission.DifferentialGeometry.Topology.exists_functional_integralLiftedSphereGenerator_eq_one

theorem bijective_zsmul_integralLiftedSphereGenerator (n : ℕ) :
    Function.Bijective (fun z : ℤ => z • integralLiftedSphereGenerator.{u} n) :=
  (isSphereHomologyGenerator_iff_bijective_zsmul n _).mp
    (integralLiftedSphereGenerator_isGenerator n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.bijective_zsmul_integralLiftedSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.bijective_zsmul_integralLiftedSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.bijective_zsmul_integralLiftedSphereGenerator ``Submission.DifferentialGeometry.Topology.bijective_zsmul_integralLiftedSphereGenerator

theorem not_bijective_zsmul_zero_sphereGenerator (n : ℕ) :
    ¬ Function.Bijective
      (fun z : ℤ => z •
        (0 : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n))) :=
  fun h => not_isSphereHomologyGenerator_zero n
    ((isSphereHomologyGenerator_iff_bijective_zsmul n 0).mpr h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_bijective_zsmul_zero_sphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_bijective_zsmul_zero_sphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_bijective_zsmul_zero_sphereGenerator ``Submission.DifferentialGeometry.Topology.not_bijective_zsmul_zero_sphereGenerator

theorem subsingleton_integralSingularHomology_two_threeSphere :
    Subsingleton (integralSingularHomology 2
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
  integralSphereHomology_subsingleton 3 2 (EuclideanSpace ℝ (Fin 4))
    (by simp) (by norm_num) (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_threeSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_threeSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_threeSphere ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_threeSphere

theorem subsingleton_integralSingularHomology_two_liftedHomotopySphere_two :
    Subsingleton (integralSingularHomology 2 (liftedHomotopySphere.{u} 2)) := by
  have h : Subsingleton (integralSingularHomology 2
      (_root_.Metric.sphere (0 : liftedSphereSpace.{u} 2) 1)) :=
    integralSphereHomology_subsingleton 3 2 (liftedSphereSpace.{u} 2)
      (liftedSphereSpace_finrank 2) (by norm_num) (by norm_num)
  exact ⟨fun a b => (integralSingularHomologyHomotopyEquiv 2
    (liftedSphereHomeomorph.{u} 2).toHomotopyEquiv).injective
      (h.allEq _ _)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_liftedHomotopySphere_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_liftedHomotopySphere_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_liftedHomotopySphere_two ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_liftedHomotopySphere_two

theorem not_subsingleton_integralSingularHomology_two_twoSphere :
    ¬ Subsingleton (integralSingularHomology 2
      (_root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  intro h
  let e := integralSphereTopHomologyEquiv 1 (EuclideanSpace ℝ (Fin 3)) (by simp)
  have : Subsingleton ℤ :=
    ⟨fun a b => e.symm.injective (h.allEq (e.symm a) (e.symm b))⟩
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (this.allEq 0 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_twoSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_twoSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_twoSphere ``Submission.DifferentialGeometry.Topology.not_subsingleton_integralSingularHomology_two_twoSphere

end DifferentialGeometry.Topology
