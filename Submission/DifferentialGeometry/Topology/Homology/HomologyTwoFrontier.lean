import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CochainCones
import Submission.DifferentialGeometry.Topology.Homology.HurewiczFrontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem subsingleton_integralSingularHomology_two_of_subsingleton_homotopyGroup_two
    [Nonempty X] (h : SphereHurewiczTwoCanonical X)
    (hpi : ∀ x : X, Subsingleton (HomotopyGroup (Fin 2) X x)) :
    Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hb := (sphereHurewicz_two_isomorphism_of_canonical_generator h x
    (integralLiftedSphereGenerator 1) (integralLiftedSphereGenerator_isGenerator 1)).1
  obtain ⟨a', rfl⟩ := hb.2 a
  obtain ⟨b', rfl⟩ := hb.2 b
  exact congrArg (sphereHurewicz 1 x (integralLiftedSphereGenerator 1))
    (Subsingleton.elim a' b')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_homotopyGroup_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_homotopyGroup_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_homotopyGroup_two ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_subsingleton_homotopyGroup_two

theorem subsingleton_integralSingularHomology_two_of_cohomology_one
    (e : integralSingularHomology 2 X ≅ integralSingularCohomology 1 X)
    [Subsingleton (integralSingularCohomology 1 X)] :
    Subsingleton (integralSingularHomology 2 X) := by
  refine ⟨fun a b => ?_⟩
  have hb : Function.Bijective
      (e.hom.hom : integralSingularHomology 2 X → integralSingularCohomology 1 X) :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  exact hb.1 (Subsingleton.elim _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_cohomology_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_cohomology_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_cohomology_one ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_cohomology_one

theorem subsingleton_integralSingularHomology_two_of_poincareDual [SimplyConnectedSpace X]
    (e : integralSingularHomology 2 X ≅ integralSingularCohomology 1 X) :
    Subsingleton (integralSingularHomology 2 X) :=
  haveI : Subsingleton (integralSingularCohomology 1 X) :=
    integralSingularCohomology_one_subsingleton (X := X)
  subsingleton_integralSingularHomology_two_of_cohomology_one e

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_poincareDual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_poincareDual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_poincareDual ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_poincareDual

theorem subsingleton_integralSingularHomology_two_of_injective_cohomology_one
    [SimplyConnectedSpace X]
    (f : integralSingularHomology 2 X →ₗ[ℤ] integralSingularCohomology 1 X)
    (hf : Function.Injective f) :
    Subsingleton (integralSingularHomology 2 X) :=
  @Function.Injective.subsingleton _ _ f hf
    (integralSingularCohomology_one_subsingleton (X := X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_cohomology_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_cohomology_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_cohomology_one ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_cohomology_one

theorem subsingleton_integralSingularHomology_two_of_injective_intersection_pairing
    [SimplyConnectedSpace X]
    (β : integralSingularHomology 2 X →ₗ[ℤ] (integralSingularHomology 1 X →ₗ[ℤ] ℤ))
    (hβ : Function.Injective β) :
    Subsingleton (integralSingularHomology 2 X) :=
  haveI : Subsingleton (integralSingularHomology 1 X) :=
    integralSingularHomology_one_subsingleton (X := X)
  @Function.Injective.subsingleton _ _ β hβ inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_intersection_pairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_intersection_pairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_intersection_pairing ``Submission.DifferentialGeometry.Topology.subsingleton_integralSingularHomology_two_of_injective_intersection_pairing

end DifferentialGeometry.Topology
